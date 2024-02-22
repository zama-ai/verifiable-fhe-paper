load("plonk.sage")
load("gates.sage")

class PolyGates:
    def __init__(self, N):
        self.gates = [Inp() for _ in range(N)]
    
    def get_N(self):
        return len(self.gates)
    
    def _compute_ntt_fw(self, poly):
        N = poly.parent().degree()
        circuit = Circuit(Gate.F, [], N=self.get_N())
        in_gates = [Inp() for _ in range(N)]
        ntt_gates = circuit.ntt_forward(in_gates)
        
        circuit.add_out_gates(ntt_gates)
        circuit.assign_gids()
        
        inp = Circuit.set_poly_inp(in_gates, poly)
        circuit_data = circuit.generate_circuit_data(in_gates)
        trace_data = circuit.get_trace(inp)
        plonk_data = tuple(list(trace_data) + list(circuit_data))
        
        ntt = vector(Gate.F, [c.out_value for c in ntt_gates])
        return ntt
    
    def _compute_ntt_bw(self, poly):
        N = poly.parent().degree()
        circuit = Circuit(Gate.F, [], N=self.get_N())
        in_gates = [Inp() for _ in range(N)]
        ntt_gates = circuit.ntt_backward(in_gates)
        
        circuit.add_out_gates(ntt_gates)
        circuit.assign_gids()
        
        inp = Circuit.set_poly_inp(in_gates, poly)
        circuit_data = circuit.generate_circuit_data(in_gates)
        trace_data = circuit.get_trace(inp)
        plonk_data = tuple(list(trace_data) + list(circuit_data))
        
        ntt = vector(Gate.F, [c.out_value for c in ntt_gates])
        return ntt
    
    def set_input(self, poly, ntt=False):
        poly_ = self._compute_ntt_fw(poly) if ntt else poly
        return {gate.gid : p for gate, p in zip(self.gates, poly_)}
    
    def flatten(self):
        return self.gates

class GLweGates:
    
    def __init__(self, k, N):
        self.poly_gates = [PolyGates(N) for _ in range(k + 1)]
    
    def get_kplus1(self):
        return len(self.poly_gates)
    
    def set_input(self, glwe_input, ntt=False):
        inp = {}
        for ginput, gate in zip(glwe_input, self.poly_gates):
            inp.update(gate.set_input(ginput, ntt))
        return inp
    
    def flatten(self):
        return sum([gate.flatten() for gate in self.poly_gates], [])
    
    def to_lists(self):
        return [poly.gates for poly in self.poly_gates]

class GLevGates:
    def __init__(self, k, N, ell):
        self.glwe_gates = [GLweGates(k, N) for _ in range(ell)]
    
    def columns(self):
        return [[gates.poly_gates[index].gates for gates in self.glwe_gates] for index in range(self.glwe_gates[0].get_kplus1())]
    
    def set_input(self, glev_input, ntt=False):
        inp = {}
        for ginput, gate in zip(glev_input, self.glwe_gates):
            inp.update(gate.set_input(ginput, ntt))
        return inp
    
    def flatten(self):
        return sum([gate.flatten() for gate in self.glwe_gates], [])

class GGswGates:
    def __init__(self, k, N, ell):
        self.glev_gates = [GLevGates(k, N, ell) for _ in range(k + 1)]
    
    def flatten(self):
        return sum([gate.flatten() for gate in self.glev_gates], [])
    
    def set_input(self, ggsw_input, ntt=False):
        inp = {}
        for ginput, gate in zip(ggsw_input, self.glev_gates):
            inp.update(gate.set_input(ginput, ntt))
        return inp

class Circuit:
    decomp_base = 256
    decomp_ell = 8
    
    # ~ ks_decomp_base = 8

    def __init__(self, F, out_gates, plookup=False, N=None):
        self.F = F
        self.out_gates = out_gates
        self.constant_gates = {}
        self.gates_with_out_zero = []
        self.plookup = plookup
        self.ntt_twiddles = {}
        self.ntt_twiddles_inv = {}
        if self.plookup:
            self.gates_w_lookup_out_wires = []
        
        if N:
             p = F.order()
             self.omega = F.multiplicative_generator()^((p - 1) // (2 * N))
             self.N = N
             

    def get_constant_gate(self, const):
        if not const in self.constant_gates:
            self.constant_gates[const] = Cnt(const)
        return self.constant_gates[const]
    
    def _virtual_out_gates(self):
        return self.out_gates + self.gates_with_out_zero
    
    def add_out_gates(self, out_gates):
        self.out_gates += out_gates
    
    def assign_gids(self):
        for gate in self._virtual_out_gates():
            gate.clear()
        
        gstart = 0
        istart = -1
        for gate in self._virtual_out_gates():
            gstart, istart = gate.assign_gids(gstart, istart)
    
    def get_wires(self):
        t = cputime()
        wires = {}
        for gate in self._virtual_out_gates():
            for out_wire, in_wires in gate.get_wires().items():
                Gate._insert_append(wires, out_wire, in_wires)
        
        wire_lst = []
        for out_wire, in_wires in wires.items():
            wire_lst.append(tuple([out_wire] + list(set(in_wires))))
        return wire_lst
    
    def get_empty_wires(self):
        empty_wires = []
        for gate in self._virtual_out_gates():
            empty_wires += gate.collect_empty_wires()
        return empty_wires
    
    def get_trace(self, inp):
        trace_dic = {}
        witnesses = {}
        for gate in self._virtual_out_gates():
            t, w = gate.get_trace(inp)
            trace_dic.update(t)
            witnesses.update(w)
        
        for gate in self.gates_with_out_zero:
            assert gate.out_value == self.F(0), f"out value of gate should be zero but is {gate.out_value.lift_centered()}"
        
        gids = sorted(trace_dic)
        assert gids == list(range(len(gids))), f"malformed gids: {gids}"
        
        trace = []
        for gid in gids:
            trace.append(trace_dic[gid])
        
        wtn_list = [x[1] for x in sorted(witnesses.items())[::-1]]
        
        outp_list = []
        for gate in self.out_gates:
            outp_list.append(gate.out_value)
        
        inp_list = [x[1] for x in sorted(inp.items())[::-1]] + outp_list
        if self.gates_with_out_zero or self.empty_wires:
            inp_list.append(self.F(0))
        
        return trace, inp_list, wtn_list
    
    def clear_trace(self):
        for gate in self._virtual_out_gates():
            gate.clear_trace()
    
    def print_circuit(self):
        for i, gate in enumerate(self.out_gates):
            print(f"out gate # {i}:")
            gate.print_circuit()
        
        for i, gate in enumerate(self.gates_with_out_zero):
            print(f"gate with out zero # {i}:")
            gate.print_circuit()
    
    def generate_circuit_data(self, inp_gates):
        t = cputime()
        selector_add = {}
        selector_mul = {}
        selector_con = {}
        for gate in self._virtual_out_gates():
            selector_add.update(gate.get_selector(GateType.ADD))
            selector_mul.update(gate.get_selector(GateType.MUL))
            selector_con.update(gate.get_selector(GateType.CNT))
        
        C = len(selector_add)
        I = len(inp_gates) + 1
        
        wires = []
        for i, gate in enumerate(self.out_gates):
            out_id = -I
            I += 1
            wires.append((out_id, gate._out_wire()))
        
        # zero checks
        self.empty_wires = self.get_empty_wires()
        if self.gates_with_out_zero or self.empty_wires:
            zero_out_id = -I
            I += 1
            
            zero_wires = [zero_out_id]
            zero_wires += [gate._out_wire() for gate in self.gates_with_out_zero]
            zero_wires += list(set(self.empty_wires))
            wires.append(tuple(zero_wires))
        
        istart = -I
        for gate in self._virtual_out_gates():
            istart = gate.assign_wtn_gids(istart)
        wires += self.get_wires()
        # number of witnesses
        W = -istart - I
        
        lu_data = None
        if self.plookup:
            lu_selector = {gate._out_wire() : 1 for gate in self.gates_w_lookup_out_wires}
            table = list(range(-Circuit.decomp_base // 2, Circuit.decomp_base // 2 + 1))
            lu_data = lu_selector, table
        return C, I - 1, W, (selector_add, selector_mul, selector_con), wires, lu_data
    
    def print_plonk_data(self, trace, inp_list, wtn_list, C, I, W, selectors, wires, lu_data):
        print(f"inputs: {[inp.lift_centered() for inp in inp_list]}")
        print(f"witness: {[wtn.lift_centered() for wtn in wtn_list]}")
        print("trace:")
        for row in trace:
            print([self.F(r).lift_centered() for r in row])
        
        print("selectors:")
        print(sorted(selectors[0].items()))
        print(sorted(selectors[1].items()))
        print(sorted(selectors[2].items()))
        
        print("wires:", wires)
        
        if lu_data != None:
            lu_selector, table = lu_data
            print(f"LU selector:{lu_selector}")
            print(f"table: {table}")
        
        print(f"Circuit data generated. Parameters (C, I, W) = {(C, I, W)}. Ready to plonk.")

    def setup():
        pcs = PolyFRI(p, beta, ell)
        plonk = Plonk(pcs)
        F = plonk.P.base_ring()
        Gate.F = F
        Gate.max_fan_in = plonk.columns - 1
        Gate.decomp_base = Circuit.decomp_base
        Gate.decomp_ell = Circuit.decomp_ell
        return plonk
    
    def test_basic():
        plonk = Circuit.setup()
        
        in_gates = [Inp(),  Inp()]
        add_gate1 = Add(in_gates[0], in_gates[1])
        const_gate = Cnt(-1)
        add_gate2 = Add(in_gates[1], const_gate)

        mul_gate = Mul(add_gate1, add_gate2)
        add_gate3 = Add(add_gate1, add_gate2)
        out_gates = [mul_gate, add_gate3]
        
        F = plonk.P.base_ring()
        circuit = Circuit(F, out_gates)
        circuit.assign_gids()
        circuit.print_circuit()
        
        inp = {in_gates[0].gid : F(5), in_gates[1].gid : F(6)}
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        circuit.print_plonk_data(*trace_data, *circuit_data)
        
        prf = plonk.prove(pinput, *trace_data)
        print("Proof generated.")
        
        assert plonk.verify(vinput, prf)
    
    def test_zero_test():
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [])
        print(len(circuit.out_gates))
        in_gates = [Inp() for _ in range(2)]
        add_gate1 = Add(in_gates[0], in_gates[1])
        const_gate = circuit.get_constant_gate(-1)
        add_gate2 = Add(in_gates[1], const_gate)

        mul_gate = Mul(add_gate1, add_gate2)
        add_gate3 = Add(add_gate1, add_gate2)
        circuit.add_out_gates([mul_gate])
        print(len(circuit.out_gates))
        
        circuit.gates_with_out_zero.append(add_gate3)
        print(len(circuit.out_gates))
        circuit.assign_gids()
        print(len(circuit.out_gates))
        
        circuit.print_circuit()
        
        inp = {in_gate.gid : i for in_gate, i in zip(in_gates, [F(5),  F(-2)])}
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        circuit.print_plonk_data(*trace_data, *circuit_data)
        
        prf = plonk.prove(pinput, *trace_data)
        print("Proof generated.")
        
        assert plonk.verify(vinput, prf)
    
    def neg_gate(self, in_gate):
        return Mul(in_gate, self.get_constant_gate(-1))
    
    def test_neg():
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [])
        in_gate = Inp()
        neg = circuit.neg_gate(in_gate)
        
        circuit.add_out_gates([neg])
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data([in_gate])
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        inp = {in_gate.gid : F.random_element()}
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        circuit.print_plonk_data(*trace_data, *circuit_data)
        
        assert -1 * inp[in_gate.gid] == neg.out_value
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def add_gate_n(in_gates):
        if len(in_gates) == 1:
            return in_gates[0]
        
        right = Circuit.add_gate_n(in_gates[1:])
        return Add(in_gates[0], right)

    def test_add_n(n = 10):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        in_gates = [Inp() for _ in range(n)]
        out_gate = Circuit.add_gate_n(in_gates)
        circuit = Circuit(F, [out_gate])
        circuit.assign_gids()
        
        inp = {in_gate.gid : F.random_element() for in_gate in in_gates}
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        assert(sum(inp.values()) == out_gate.out_value)
        
        circuit.print_plonk_data(*trace_data, *circuit_data)
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def mul_gate_n(in_gates):
        if len(in_gates) == 1:
            return in_gates[0]
        
        right = Circuit.mul_gate_n(in_gates[1:])
        return Mul(in_gates[0], right)

    def test_mul_n(n = 10):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        in_gates = [Inp() for _ in range(n)]
        out_gate = Circuit.mul_gate_n(in_gates)
        circuit = Circuit(F, [out_gate])
        circuit.assign_gids()
        
        inp = {in_gate.gid : F.random_element() for in_gate in in_gates}
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        assert(prod(inp.values()) == out_gate.out_value)
        
        circuit.print_plonk_data(*trace_data, *circuit_data)
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
        
    def inner_prod_gate(inp1, inp2):
        mul_gates = [Mul(in1, in2) for in1, in2 in zip(inp1, inp2)]
        return Circuit.add_gate_n(mul_gates)
    
    def test_inner(n=10):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        in1_gates = [Inp() for _ in range(n)]
        in2_gates = [Inp() for _ in range(n)]
        out_gate = Circuit.inner_prod_gate(in1_gates, in2_gates)
        circuit = Circuit(F, [out_gate])
        circuit.assign_gids()
        
        inp = {in_gate.gid : F.random_element() for in_gate in in1_gates + in2_gates}
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in1_gates + in2_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        vin1 = vector(F, list(inp.values())[:n])
        vin2 = vector(F, list(inp.values())[n:])
        assert(vector(F, vin1) * vector(F, vin2) == out_gate.out_value)
        
        circuit.print_plonk_data(*trace_data, *circuit_data)
        
        prf = plonk.prove(pinput, *trace_data)
        assert(plonk.verify(vinput, prf))
    
    def range_check(self, in_gate, L, U):
        c_gates = [self.get_constant_gate(i) for i in range(-U, -L + 1)]
        add_gates = [Add(in_gate, gate) for gate in c_gates]
        mul_gate = Circuit.mul_gate_n(add_gates)
        self.gates_with_out_zero.append(mul_gate)
    
    def test_range():
        B = 2
        n = 2
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [])
        in_gates = [Inp() for _ in range(n)]
        for gate in in_gates:
            circuit.range_check(gate, -B - 1, B + 1)
        add = Circuit.add_gate_n(in_gates)
        circuit.add_out_gates([add])
        circuit.assign_gids()
        
        inp = {gate.gid : F(randint(-B, B)) for gate in in_gates}
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        circuit.print_plonk_data(*trace_data, *circuit_data)
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def gadget_decomp(self, in_gate, base=None, ell=None):
        if base == None:
            base = Circuit.decomp_base
        if ell == None:
            ell = Circuit.decomp_ell
        
        witness_gates = [Wtn() for _ in range(ell)]
        if self.plookup:
            self.gates_w_lookup_out_wires += witness_gates
        else:
            for gate in witness_gates:
                self.range_check(gate, -base // 2, base // 2)
        base_power_gates = [self.get_constant_gate(-base^i) for i in range(ell)]
        in_gate.decomposes_into = witness_gates
        for gate in witness_gates:
            gate.decomposes = in_gate
        recomb = Circuit.inner_prod_gate(witness_gates, base_power_gates)
        add_gate = Add(in_gate, recomb)
        self.gates_with_out_zero.append(add_gate)
        
        return witness_gates
    
    def test_decomp(ell=None):
        if ell == None:
            ell = Circuit.decomp_ell
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=True)
        in_gate = Inp()
        decomp_terms = circuit.gadget_decomp(in_gate)
        sum_gate = Circuit.add_gate_n(decomp_terms)
        circuit.add_out_gates([sum_gate])
        
        circuit.assign_gids()
        
        inp = {in_gate.gid : F.random_element()}
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data([in_gate])
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        circuit.print_plonk_data(*trace_data, *circuit_data)
        
        decomp_gates = in_gate.decomposes_into
        decomp_vector = vector([gate.out_value for gate in decomp_gates][-ell:])
        base_vector = vector(F, [Circuit.decomp_base^i for i in range(Circuit.decomp_ell)][-ell:])
        
        bound = Circuit.decomp_base^(Circuit.decomp_ell - ell)
        
        assert abs((base_vector * decomp_vector - in_gate.out_value).lift_centered()) < bound, f"{abs((base_vector * decomp_vector - in_gate.out_value).lift_centered())} > {bound}"
        
        prf = plonk.prove(pinput, *trace_data)
        print(f"Proof size: {plonk.proof_size(prf)}")
        assert plonk.verify(vinput, prf)
    
    def binary_decomp(self, in_gate, nbits=None):
        if not nbits:
            p = self.F.order()
            nbits = int(ceil(p.log(2)))
        witness_gates = [Wtn() for _ in range(nbits)]
        for gate in witness_gates:
            self.range_check(gate, 0, 1)
        base_power_gates = [self.get_constant_gate(-2^i) for i in range(nbits)]
        
        in_gate.decomp_type = DecompType.BINARY
        in_gate.decomposes_into = witness_gates
        for gate in witness_gates:
            gate.decomposes = in_gate
        recomb = Circuit.inner_prod_gate(witness_gates, base_power_gates)
        add_gate = Add(in_gate, recomb)
        self.gates_with_out_zero.append(add_gate)
        
        return witness_gates
    
    def test_bin_decomp(nbits=5):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=False)
        in_gate = Inp()
        decomp_terms = circuit.binary_decomp(in_gate, nbits)
        sum_gate = Circuit.add_gate_n(decomp_terms)
        circuit.add_out_gates([sum_gate])
        
        circuit.assign_gids()
        
        inp = {in_gate.gid : F(randint(0, 2 ** nbits - 1))}
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data([in_gate])
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        decomp_vector = vector([gate.out_value for gate in in_gate.decomposes_into])
        base_vector = vector(F, [2^i for i in range(nbits)])
        
        assert base_vector * decomp_vector == in_gate.out_value, f"binary decomposition incorrect"
        
        prf = plonk.prove(pinput, *trace_data)
        print(f"Proof size: {plonk.proof_size(prf)}")
        assert plonk.verify(vinput, prf)
    
    # poly arithmetic mod X^N + 1
    def poly_add(inp1, inp2):
        add_gates = [Add(in1, in2) for in1, in2 in zip(inp1, inp2)]
        return add_gates
    
    def test_poly_add(n = 10):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        
        in1_gates = [Inp() for _ in range(n)]
        in2_gates = [Inp() for _ in range(n)]
        
        out_gates = Circuit.poly_add(in1_gates, in2_gates)
        circuit = Circuit(F, out_gates)
        circuit.assign_gids()
        
        inp = {in_gate.gid : F.random_element() for in_gate in in1_gates + in2_gates}
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in1_gates + in2_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        vin1 = vector(F, list(inp.values())[:n])
        vin2 = vector(F, list(inp.values())[n:])
        assert vector(F, vin1) + vector(F, vin2) == vector(F, [c.out_value for c in out_gates])
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf) 
    
    def poly_add_n(in_gates):
        if len(in_gates) == 1:
            return in_gates[0]
        
        right = Circuit.poly_add_n(in_gates[1:])
        return Circuit.poly_add(in_gates[0], right)
    
    def test_poly_add_n(N=2, n=4):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        
        in_gates = [[Inp() for _ in range(N)] for _ in range(n)]
        out_gates = Circuit.poly_add_n(in_gates)
        circuit = Circuit(F, out_gates)
        circuit.assign_gids()
        
        inp = {in_gate.gid : F.random_element() for in_gate in sum(in_gates, [])}
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(sum(in_gates, []))
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        vins = [vector(F, list(inp.values())[i*N:(i+1)*N]) for i in range(n)]
        assert sum(vins) == vector(F, [c.out_value for c in out_gates])
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def poly_pairwise_mul(inp1, inp2):
        return [Mul(in1, in2) for in1, in2 in zip(inp1, inp2)]
    
    def poly_mul(self, inp1, inp2):
        ntt1 = self.ntt_forward(inp1)
        ntt2 = self.ntt_forward(inp2)
        
        ntt = Circuit.poly_pairwise_mul(ntt1, ntt2)
        
        return self.ntt_backward(ntt)
    
    def _bit_reverse_index(index, log_size):
        return int(bin(index)[2:][::-1].ljust(log_size, '0'), 2)
    
    def ntt_forward(self, inp):
        N = len(inp)
        logN = log(N, 2)
        
        if N not in self.ntt_twiddles:
            self.ntt_twiddles[N] = [self.omega^Circuit._bit_reverse_index(i, logN) for i in range(N)]
        
        twiddles = self.ntt_twiddles[N]
        
        a = [inp]
        t = N
        for m in [2^i for i in range(logN)]:
            a_out = [None for _ in range(N)]
            t /= 2
            for i in range(m):
                j1 = 2 * i * t
                j2 = j1 + t - 1
                S = self.get_constant_gate(twiddles[m + i])
                for j in range(j1, j2 + 1):
                    U = a[-1][j]
                    V = Mul(a[-1][j + t], S)
                    a_out[j] = Add(U, V)
                    nV = self.neg_gate(V)
                    a_out[j + t] = Add(U, nV)
            a.append(a_out)
        return a[-1]
    
    def ntt_backward(self, inp):
        N = len(inp)
        logN = log(N, 2)
        
        if N not in self.ntt_twiddles_inv:
            self.ntt_twiddles_inv[N] = [self.omega^(-Circuit._bit_reverse_index(i, logN)) for i in range(N)]
        
        twiddles = self.ntt_twiddles_inv[N]
        
        a = [inp]
        t = 1
        for m in [2^i for i in range(1, logN + 1)][::-1]:
            a_out = [None for _ in range(N)]
            j1 = 0
            h = m / 2
            for i in range(h):
                j2 = j1 + t - 1
                S = self.get_constant_gate(twiddles[h + i])
                for j in range(j1, j2 + 1):
                    U = a[-1][j]
                    V = a[-1][j + t]
                    a_out[j] = Add(U, V)
                    nV = self.neg_gate(V)
                    diff = Add(U, nV)
                    a_out[j + t] = Mul(diff, S)
                j1 += 2 * t
            t *= 2
            a.append(a_out)
        
        Ninv = self.get_constant_gate(self.F(N)^(-1))
        return [Mul(Ninv, ai) for ai in a[-1]]
    
    def test_ntt(N):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        
        circuit = Circuit(F, [], N=N)
        in_gates = [Inp() for _ in range(N)]
        ntt_gates = circuit.ntt_forward(in_gates)
        out_gates = circuit.ntt_backward(ntt_gates)
        
        circuit.add_out_gates(out_gates)
        circuit.assign_gids()
        
        # ~ circuit.print_circuit()
        
        inp = {in_gate.gid : F.random_element() for in_gate in in_gates}
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        print(f"Circuit data generated. Parameters (C, I, W, d) = {(circuit_data[0], circuit_data[1], circuit_data[2], plonk.d)}. Ready to plonk.")
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        vin = vector(F, list(inp.values()))
        
        ntt = vector(F, [c.out_value for c in ntt_gates])
        out = vector(F, [c.out_value for c in out_gates])
        
        assert vin == out
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf) 
    
    def set_poly_inp(in_gates, poly):
        return {gate.gid : p for gate, p in zip(in_gates, poly)}
    
    def test_poly_mul(N = 8):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], N=N)
        in1_gates = [Inp() for _ in range(N)]
        in2_gates = [Inp() for _ in range(N)]
        
        out_gates = circuit.poly_mul(in1_gates, in2_gates)
        circuit.add_out_gates(out_gates)
        circuit.assign_gids()
        
        R.<y> = plonk.P.quotient(x^N + 1)
        a = R.random_element()
        b = R.random_element()
        inp = Circuit.set_poly_inp(in1_gates, a)
        inp.update(Circuit.set_poly_inp(in2_gates, b))
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in1_gates + in2_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        circuit.print_plonk_data(*trace_data, *circuit_data)
        
        c = a*b
        print(vector(c))
        print(vector(F, [gate.out_value for gate in out_gates]))
        assert c == R([gate.out_value for gate in out_gates])
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def poly_decomp(self, in_poly):
        decomp_terms = []
        for gate in in_poly:
            decomp_terms.append(self.gadget_decomp(gate))
        out_polys = []
        for ell in range(Circuit.decomp_ell):
            out_polys.append([term[ell] for term in decomp_terms])
        return out_polys
    
    def test_poly_decomp(N=2):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=True, N=N)
        in_gates = [Inp() for _ in range(N)]
        decomp_terms = circuit.poly_decomp(in_gates)
        sum_gates = Circuit.poly_add_n(decomp_terms)
        circuit.add_out_gates(sum_gates)
        circuit.assign_gids()
        
        inp = {in_gate.gid : F.random_element() for in_gate in in_gates}
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        decomp_gates = [in_gate.decomposes_into for in_gate in in_gates]
        base_vector = vector(F, [Circuit.decomp_base^i for i in range(Circuit.decomp_ell)])
        
        for i, in_gate in enumerate(in_gates):
            decomp_vector = vector([gate.out_value for gate in decomp_gates[i]])
            for v in decomp_vector:
                v_ = v.lift_centered()
                assert -Circuit.decomp_base // 2 <= v_ and v_ <= Circuit.decomp_base // 2, f"base: {Circuit.decomp_base}, vector: {decomp_vector}"
            assert base_vector * decomp_vector == in_gate.out_value
        
        prf = plonk.prove(pinput, *trace_data)
        print(f"Proof size: {plonk.proof_size(prf)}")
        assert plonk.verify(vinput, prf)
    
    # assumes inputs are in ntt domain and output will be in ntt domain
    def poly_inner(self, inp1, inp2):
        mul_gates = [Circuit.poly_pairwise_mul(gate1, gate2) for gate1, gate2 in zip(inp1, inp2)]
        return Circuit.poly_add_n(mul_gates)
        
    def test_poly_inner(N=4, n=8):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], N=N)
        in_gates1 = [[Inp() for _ in range(N)] for _ in range(n)]
        in_gates2 = [[Inp() for _ in range(N)] for _ in range(n)]
        
        out_gates = circuit.poly_inner(in_gates1, in_gates2)
        circuit.add_out_gates(out_gates)
        circuit.assign_gids()
        
        R.<y> = plonk.P.quotient(x^N + 1)
        in_polys1 = [R.random_element() for _ in range(n)]
        in_polys2 = [R.random_element() for _ in range(n)]
        out_poly = sum([vector(F, p1).pairwise_product(vector(F, p2)) for p1, p2 in zip(in_polys1, in_polys2)])
        
        inp = {}
        for gates, poly in zip(in_gates1 + in_gates2, in_polys1 + in_polys2):
            inp.update(Circuit.set_poly_inp(gates, poly))
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(sum(in_gates1 + in_gates2, []))
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        for out_gate, out_value in zip(out_gates, out_poly):
            assert out_gate.out_value == out_value
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def glev_mul(self, glwe_poly, glev_polys, pbs_ell=None):
        if pbs_ell == None:
            pbs_ell=Circuit.decomp_ell
        decomp = self.poly_decomp(glwe_poly)
        
        decomp_hat = [self.ntt_forward(decompi) for decompi in decomp[-pbs_ell:]]
        # ~ return [self.ntt_backward(self.poly_inner(decomp_hat, glev_column)) for glev_column in glev_polys.columns()]
        return [self.poly_inner(decomp_hat, glev_column) for glev_column in glev_polys.columns()]
    
    def test_glev_mul(N=8, k=1, pbs_ell=None):
        if pbs_ell == None:
            pbs_ell=Circuit.decomp_ell
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=True, N=N)
        glwe_in_gates = PolyGates(N)
        glev_in_gates = GLevGates(k, N, pbs_ell)
        
        out_gates = circuit.glev_mul(glwe_in_gates.gates, glev_in_gates, pbs_ell)
        circuit.add_out_gates(sum(out_gates, []))
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(glwe_in_gates.gates + glev_in_gates.flatten())
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        prfs = []
        for _ in range(2):
            R.<y> = plonk.P.quotient(x^N + 1)
            glwe_input = R.random_element()
            bs = [R([randint(0,1) for _ in range(N)]) for _ in range(k + 1)]
            glev_inputs = [[b * Circuit.decomp_base^i for b in bs] for i in range(Circuit.decomp_ell - pbs_ell, Circuit.decomp_ell)]
            inp = glwe_in_gates.set_input(glwe_input)
            
            inp.update(glev_in_gates.set_input(glev_inputs, ntt=True))
            
            print("Generating trace data")
            trace_data = circuit.get_trace(inp)
            
            bound = Circuit.decomp_base^(Circuit.decomp_ell - pbs_ell + 1)
            for b, out_gate in zip(bs, out_gates):
                out_hat = glwe_in_gates._compute_ntt_bw(R([gate.out_value for gate in out_gate]))
                for out_val, val in zip(out_hat, glwe_input * b):
                    assert abs((out_val - val).lift_centered()) < bound, f"{abs((out_val - val).lift_centered())} >= {bound}"
            
            print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
            print(f"max out gid: {max([gate.gid for gate in circuit._virtual_out_gates()])}")
            
            t = cputime()
            prfs.append(plonk.prove(pinput, *trace_data))
            print(f"Generated plonk proof in {cputime(t)}s.")
            print(f"Proof size: {plonk.proof_size(prfs[-1])} hash values and field elements")
            circuit.clear_trace()
        
        for prf in prfs:
            assert plonk.verify(vinput, prf)
        
    def glwe_neg(self, glwe):
        return [self.poly_neg(poly) for poly in glwe]
    
    def glwe_add(glwe_left, glwe_right):
        return [Circuit.poly_add(left, right) for left, right in zip(glwe_left, glwe_right)]
    
    def glwe_add_n(glwe_polys):
        if len(glwe_polys) == 1:
            return glwe_polys[0]
        
        right = Circuit.glwe_add_n(glwe_polys[1:])
        return Circuit.glwe_add(glwe_polys[0], right)
    
    def test_glwe_arithmetic(N=8, k=1, n=4):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], N=N)
        glwe_in_gates = [GLweGates(k, N) for _ in range(n)]
        
        neg = circuit.glwe_neg(glwe_in_gates[0].to_lists())
        out_gates = Circuit.glwe_add_n([neg] + [gate.to_lists() for gate in glwe_in_gates[1:]])
        
        circuit.add_out_gates(sum(out_gates, []))
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(sum([gate.flatten() for gate in glwe_in_gates], []))
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print(f"Circuit data generated. Parameters (C, I, d) = {(circuit_data[0], circuit_data[1] + circuit_data[2], plonk.d)}. Ready to plonk.")
        print(f"max out gid: {max([gate.gid for gate in circuit._virtual_out_gates()])}")
        
        print("Generating inputs")
        R.<y> = plonk.P.quotient(x^N + 1)
        glwe_inputs = [[R.random_element() for _ in range(k + 1)] for _ in glwe_in_gates]
        inp = {}
        for glwe_in_gate, glwe_input in zip(glwe_in_gates, glwe_inputs):
            inp.update(glwe_in_gate.set_input(glwe_input))
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        expected = vector(R, [-1] + [1] * (n - 1)) * matrix(R, glwe_inputs)
        
        for out_gate, ex in zip(out_gates, expected):
            for gate, val in zip(out_gate, ex):
                assert gate.out_value == val, f"incorrect glwe arithmetic: {gate.out_value} != {val}"
        
        
        t = cputime()
        prf = plonk.prove(pinput, *trace_data)
        print(f"Generated plonk proof in {cputime(t)}s.")
        print(f"Proof size: {plonk.proof_size(prf)} hash values and field elements")
        
        assert plonk.verify(vinput, prf)
    
    def external_product(self, glwe_polys, ggsw_polys, pbs_ell=2):
        glev_muls = [self.glev_mul(glwe_poly, glev_polys, pbs_ell) for glwe_poly, glev_polys in zip(glwe_polys, ggsw_polys.glev_gates)]
        sum_polys = Circuit.glwe_add_n(glev_muls[:-1])
        return [self.ntt_backward(poly) for poly in Circuit.glwe_add(glev_muls[-1], self.glwe_neg(sum_polys))]
    
    def test_external_product(N=8, k=1, pbs_ell=None):
        if pbs_ell == None:
            pbs_ell=Circuit.decomp_ell
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=True, N=N)
        glwe_in_gates = GLweGates(k, N)
        ggsw_in_gates = GGswGates(k, N, pbs_ell)
        
        out_gates = circuit.external_product(glwe_in_gates.to_lists(), ggsw_in_gates, pbs_ell)
        circuit.add_out_gates(sum(out_gates, []))
        circuit.assign_gids()
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(glwe_in_gates.flatten() + ggsw_in_gates.flatten())
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print(f"Circuit data generated. Parameters (C, I, d) = {(circuit_data[0], circuit_data[1] + circuit_data[2], plonk.d)}. Ready to plonk.")
        print(f"max out gid: {max([gate.gid for gate in circuit._virtual_out_gates()])}")
        
        prfs = []
        for _ in range(1):
            R.<y> = plonk.P.quotient(x^N + 1)
            glwe_inputs = [R.random_element() for _ in range(k + 1)]
            bs = [R([randint(0,1) for _ in range(N)]) for _ in range(k + 1)]
            ggsw_inputs = [[[b * Circuit.decomp_base^i for b in bs] for i in range(Circuit.decomp_ell - pbs_ell, Circuit.decomp_ell)] for _ in range(k + 1)]
            
            inp = glwe_in_gates.set_input(glwe_inputs)
            inp.update(ggsw_in_gates.set_input(ggsw_inputs, ntt=True))
            print("Generating trace data")
            trace_data = circuit.get_trace(inp)
            
            bound = Circuit.decomp_base^(Circuit.decomp_ell - pbs_ell + 1)
            expected = [glwe_inputs[-1] * b - sum([p * b for p in glwe_inputs[:-1]]) for b in bs]
            
            for out_gate, ex in zip(out_gates, expected):
                for gate, val in zip(out_gate, ex):
                    assert abs((gate.out_value - val).lift_centered()) < bound, f"{abs((gate.out_value - val).lift_centered())} >= {bound}"
            
            
            t = cputime()
            prfs.append(plonk.prove(pinput, *trace_data))
            print(f"Generated plonk proof in {cputime(t)}s.")
            print(f"Proof size: {plonk.proof_size(prfs[-1])} hash values and field elements")
            circuit.clear_trace()
        
        for prf in prfs:
            assert plonk.verify(vinput, prf)
    
    def cmux(self, left, right, control):
        diff = Add(left, self.neg_gate(right))
        return Add(Mul(diff, control), right)
    
    def poly_cmux(self, left, right, control):
        return [self.cmux(l, r, control) for l, r in zip(left, right)]
    
    def rotate_poly_const(self, poly, log_shift):
        shift = 2 ** log_shift
        mul_gates = [Mul(p, self.get_constant_gate(-1)) for p in poly[-shift:]]
        return mul_gates + poly[:-shift]
    
    def test_rotate_poly_const(N=16, nbits=2):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], N=N)
        in_gates = [Inp() for _ in range(N)]
        
        out_gates = circuit.rotate_poly_const(in_gates, nbits)
        circuit.add_out_gates(out_gates)
        circuit.assign_gids()
        
        R.<y> = plonk.P.quotient(x^N + 1)
        poly = R.random_element()
        
        inp = Circuit.set_poly_inp(in_gates, poly)
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        shifted_poly = y^(2^nbits) * poly
        out_poly = R([gate.out_value for gate in out_gates])
        
        assert shifted_poly == out_poly, f"shifted poly incorrect"
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    # ~ def rotate_polys(self, polys, shift, shift_nbits):
        # ~ shift_bits = self.binary_decomp(shift, shift_nbits)
        # ~ polys_steps = [polys]
        # ~ for log_shift, shift_bit in enumerate(shift_bits):
            # ~ rot_polys = [self.rotate_poly_const(poly, log_shift) for poly in polys_steps[-1]]
            # ~ polys_steps.append([self.poly_cmux(rot_poly, poly, shift_bit) for rot_poly, poly in zip(rot_polys, polys_steps[-1])])
        # ~ return polys_steps[-1]

    def rotate_polys(self, polys, element):
        # implicitely do the mod switch by selecting the logN + 1 MSBs for shifting
        N = len(polys[0])
        logN = int(round(log(N, 2)))
        shift_bits = self.binary_decomp(element)[-(logN + 1):]
        polys_steps = [polys]
        for log_shift, shift_bit in enumerate(shift_bits):
            rot_polys = [self.rotate_poly_const(poly, log_shift) for poly in polys_steps[-1]]
            polys_steps.append([self.poly_cmux(rot_poly, poly, shift_bit) for rot_poly, poly in zip(rot_polys, polys_steps[-1])])
        return polys_steps[-1]
    
    def test_rotate_polys(N=16, k=1):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], N=N)
        in_gates = [PolyGates(N) for _ in range(k + 1)]
        shift_gate = Inp()
        
        out_gates = circuit.rotate_polys([in_gate.gates for in_gate in in_gates], shift_gate)
        
        circuit.add_out_gates(sum(out_gates, []))
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(sum([in_gate.gates for in_gate in in_gates], []) + [shift_gate])
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        R.<y> = plonk.P.quotient(x^N + 1)
        polys = [R.random_element() for _ in range(k + 1)]
        shift = F.random_element()
        
        inp = {}
        for in_gate, poly in zip(in_gates, polys):
            inp.update(in_gate.set_input(poly))
        inp[shift_gate.gid] = shift
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        shift_ = shift.lift() * (2 * N) // (2^64)
        shifted_polys = [y^shift_ * poly for poly in polys]
        out_polys = [R([gate.out_value for gate in out_gate]) for out_gate in out_gates]
        
        assert all(shifted_poly == out_poly for shifted_poly, out_poly in zip(shifted_polys, out_polys)), "rotated poly incorrect"
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def poly_neg(self, poly):
        return [self.neg_gate(p) for p in poly]
    
    def blind_rot_step(self, glwe_polys, ggsw_polys, lwe_mask_element, pbs_ell=2):
        N = len(glwe_polys[0])
        # ~ shifted_glwe = self.rotate_polys(glwe_polys, lwe_mask_element, log(N, 2) + 1)
        shifted_glwe = self.rotate_polys(glwe_polys, lwe_mask_element)
        diff_glwe = Circuit.glwe_add(shifted_glwe, self.glwe_neg(glwe_polys))
        return Circuit.glwe_add(self.external_product(diff_glwe, ggsw_polys, pbs_ell), glwe_polys)
    
    def test_blind_rot_step(N=8, k=1, pbs_ell=None):
        if pbs_ell == None:
            pbs_ell = Circuit.decomp_ell
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=True, N=N)
        glwe_in_gates = GLweGates(k, N)
        ggsw_in_gates = GGswGates(k, N, pbs_ell)
        lwe_in_gate = Inp()
        
        out_gates = circuit.blind_rot_step(glwe_in_gates.to_lists(), ggsw_in_gates, lwe_in_gate, pbs_ell)
        circuit.add_out_gates(sum(out_gates, []))
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(glwe_in_gates.flatten() + ggsw_in_gates.flatten() + [lwe_in_gate])
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        print(f"Circuit data generated. Parameters (C, I, W, d) = {(circuit_data[0], circuit_data[1], circuit_data[2], plonk.d)}. Ready to plonk.")
        print(f"max out gid: {max([gate.gid for gate in circuit._virtual_out_gates()])}")
        
        R.<y> = plonk.P.quotient(x^N + 1)
        glwe_inputs = [R.random_element() for _ in range(k + 1)]
        bs = [R([randint(0,1) for _ in range(N)]) for _ in range(k + 1)]
        ggsw_inputs = [[[b * Circuit.decomp_base^i for b in bs] for i in range(Circuit.decomp_ell - pbs_ell, Circuit.decomp_ell)] for _ in range(k + 1)]
        # ~ lwe_input = randint(0, 2 * N - 1)
        lwe_input = F.random_element()
        
        inp = glwe_in_gates.set_input(glwe_inputs)
        inp.update(ggsw_in_gates.set_input(ggsw_inputs, ntt=True))
        # ~ inp[lwe_in_gate.gid] = F(lwe_input)
        inp[lwe_in_gate.gid] = lwe_input
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        bound = Circuit.decomp_base^(Circuit.decomp_ell - pbs_ell + 1)
        
        # ~ shift = lwe_input.lift() * (2 * N) // (2^64)
        shift = lwe_input.lift() * (2 * N) // F.order()
        diff = [y^shift * poly - poly for poly in glwe_inputs]
        expected = [diff[-1] * b - sum([p * b for p in diff[:-1]]) + poly for b, poly in zip(bs, glwe_inputs)]
        
        for out_gate, ex in zip(out_gates, expected):
            for gate, val in zip(out_gate, ex):
                assert abs((gate.out_value - val).lift_centered()) < bound, f"{abs((gate.out_value - val).lift_centered())} >= {bound}"
        
        t = cputime()
        prf = plonk.prove(pinput, *trace_data)
        print(f"Generated plonk proof in {cputime(t)}s.")
        print(f"Proof size: {plonk.proof_size(prf)} hash values, field elements and bytes")
        assert plonk.verify(vinput, prf)
    
    def neg_mod_2N(self, in_gate, N):
        w = Wtn()
        self.range_check(w, 0, 1)
        
        in_gate.decomp_type = DecompType.NEGMOD2N
        in_gate.decomposes_into = w
        w.decomposes = in_gate
        
        mul_gate = Mul(w, self.get_constant_gate(2 * N))
        return Add(mul_gate, self.neg_gate(in_gate))
    
    def test_neg_mod_2N(N=16, n=256):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=False, N=N)
        in_gates = [Inp() for _ in range(n)]
        out_gates = [circuit.neg_mod_2N(in_gate, N) for in_gate in in_gates]
        
        circuit.add_out_gates(out_gates)
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(in_gates)
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        
        print(f"Circuit data generated. Parameters (C, I, d) = {(circuit_data[0], circuit_data[1] + circuit_data[2], plonk.d)}. Ready to plonk.")
        print(f"max out gid: {max([gate.gid for gate in circuit._virtual_out_gates()])}")
        
        
        test_vals = [F(randint(0, 2*N - 1)) for _ in range(n)]
        inp = {gate.gid : test_val for gate, test_val in zip(in_gates, test_vals)}
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        for gate, val in zip(out_gates, test_vals):
            assert gate.out_value == (2*N - val.lift()) % (2 * N), f"incorrect modular negation: {gate.out_value} != {(2*N - val) % (2 * N)} mod {2 * N}"
        
        t = cputime()
        prf = plonk.prove(pinput, *trace_data)
        print(f"Generated plonk proof in {cputime(t)}s.")
        print(f"Proof size: {plonk.proof_size(prf)} hash values and field elements")
        assert plonk.verify(vinput, prf)
    
    def blind_rot(self, testv, lwe_ct, bsk, pbs_ell=2):
        if pbs_ell == None:
            pbs_ell = Circuit.decomp_ell
        mask = lwe_ct[:-1]
        body = lwe_ct[-1]
        
        n = len(mask)
        N = len(testv)
        # ~ body_neg = self.neg_mod_2N(body, N)
        body_neg = self.neg_gate(body)
        glwe_polys = [[[self.get_constant_gate(0) for _ in range(N)]] + self.rotate_polys([testv], body_neg)]
        for lwe_mask_element, ggsw_polys in zip(mask, bsk):
            glwe_polys.append(self.blind_rot_step(glwe_polys[-1], ggsw_polys, lwe_mask_element, pbs_ell))
        return glwe_polys[-1]

    ## split up blind rotation test for testing purposes
    def test_blind_rot_setup(N=2, k=1, n=2, pbs_ell=2):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=True, N=N)
        testv_gates = [Inp() for _ in range(N)]
        lwe_ct_gates = [Inp() for _ in range(n + 1)]
        bsk_gates = [GGswGates(k, N, pbs_ell) for _ in range(n)]
        
        out_gates = circuit.blind_rot(testv_gates, lwe_ct_gates, bsk_gates, pbs_ell)
        
        circuit.add_out_gates(sum(out_gates, []))
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(testv_gates + lwe_ct_gates + sum([ggsw.flatten() for ggsw in bsk_gates], []))
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        
        return N, k, n, pbs_ell, circuit, circuit_data, testv_gates, lwe_ct_gates, bsk_gates, plonk, pinput, vinput
    
    def test_blind_rot_prove(N, k, n, pbs_ell, circuit, circuit_data, testv_gates, lwe_ct_gates, bsk_gates, plonk, pinput, vinput):
        PlonkPoly.P = plonk.P
        PlonkPoly.TF = plonk.tf
        F = plonk.P.base_ring()
        R.<y> = plonk.P.quotient(x^N + 1)
        testv_input = R.random_element()
        bs = [R([randint(0, 1) for _ in range(N)]) for _ in range(k + 1)]
        bsk_inputs = [[[[b * Circuit.decomp_base^i for b in bs] for i in range(Circuit.decomp_ell - pbs_ell, Circuit.decomp_ell)] for _ in range(k + 1)] for _ in range(n)]
        # ~ lwe_ct_input = [randint(0, 2 * N - 1) for _ in range(n + 1)]
        lwe_ct_input = [F.random_element() for _ in range(n + 1)]
        
        inp = {gate.gid : val for gate, val in zip(testv_gates, testv_input)}
        for ggsw_gate, ggsw_input in zip(bsk_gates, bsk_inputs):
            inp.update(ggsw_gate.set_input(ggsw_input, ntt=True))
        for lwe_in_gate, lwe_input in zip(lwe_ct_gates, lwe_ct_input):
            inp[lwe_in_gate.gid] = F(lwe_input)
        
        print("Generating trace data")
        circuit.clear_trace()
        trace_data = circuit.get_trace(inp)
        
        print(f"Circuit data generated. Parameters (C, I, d) = {circuit_data[:3]}. Ready to plonk.")
        print(f"max out gid: {max([gate.gid for gate in circuit._virtual_out_gates()])}")
        
        t = cputime()
        prf = plonk.prove(pinput, *trace_data)
        print(f"Generated plonk proof in {cputime(t)}s.")
        hashes, field_elements, byts = plonk.proof_size(prf)
        print(f"Proof size: {(hashes, field_elements)} hash values and field elements for 2^{byts.log(2).n()} bytes")
        assert plonk.verify(vinput, prf)

    def test_blind_rot(N=2, k=1, n=2, pbs_ell=2):
        setup_data = Circuit.test_blind_rot_setup(N=N, k=k, n=n, pbs_ell=pbs_ell)
        Circuit.test_blind_rot_prove(*setup_data)
    
    def sample_extract(self, glwe_polys):
        lwe_ct = []
        for poly in glwe_polys[:-1]:
            lwe_ct += [poly[0]] + [self.neg_gate(ai) for ai in poly[-1:0:-1]]
        lwe_ct.append(glwe_polys[-1][0])
        return lwe_ct
    
    def test_sample_extract(N=2, k=1, pbs_ell=2):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=False, N=N)
        glwe_polys = GLweGates(k, N)
        out_gates = circuit.sample_extract(glwe_polys.to_lists())
        
        circuit.add_out_gates(out_gates)
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(glwe_polys.flatten())
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        print(f"Circuit data generated. Parameters (C, I, d) = {circuit_data[:3]}. Ready to plonk.")
        
        R.<y> = plonk.P.quotient(x^N + 1)
        s = [R([randint(0, 1) for _ in range(N)]) for _ in range(k)]
        a = [R.random_element() for _ in range(k)]
        m = R.random_element()
        b = vector(a) * vector(s) + m
        
        inp = glwe_polys.set_input(a + [b])
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        lwe_ct = [gate.out_value for gate in out_gates]
        s_ = sum([list(si) for si in s], [])
        
        m_ = lwe_ct[-1] - vector(F, lwe_ct[:-1]) * vector(F, s_)
        
        assert m_ == m[0]
        
        t = cputime()
        prf = plonk.prove(pinput, *trace_data)
        print(f"Generated plonk proof in {cputime(t)}s.")
        hashes, field_elements, byts = plonk.proof_size(prf)
        print(f"Proof size: {(hashes, field_elements)} hash values and field elements for 2^{byts.log(2).n()} bytes")
        assert plonk.verify(vinput, prf)
    
    def scalar_vector_mul(scalar, vec):
        return [Mul(scalar, vi) for vi in vec]
    
    def add_vec_n(in_gates):
        if len(in_gates) == 1:
            return in_gates[0]
        
        right = Circuit.add_vec_n(in_gates[1:])
        return [Add(left, right) for left, right in zip(in_gates[0], right)]

    def test_add_vec_n(n=10, t=100):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        in_gates = [[Inp() for _ in range(t)] for _ in range(n)]
        out_gates = Circuit.add_vec_n(in_gates)
        circuit = Circuit(F, out_gates)
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(sum(in_gates, []))
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
        print(f"Plonk parameter d and d_max: {plonk.d}, {plonk.d_max}")
        V = VectorSpace(F, t)
        vecs = [V.random_element() for _ in range(n)]
        
        inp = {}
        for vec, gate in zip(vecs, in_gates):
            inp.update({g.gid : vi for vi, g in zip(vec, gate)})
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        assert sum(vecs) == V([out_gate.out_value for out_gate in out_gates])
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def glev_inner(self, a, glev, ks_ell):
        # ~ a_decomp = self.gadget_decomp(a, base=Circuit.ks_decomp_base)[-ks_ell:]
        a_decomp = self.gadget_decomp(a)[-ks_ell:]
        vecs = [Circuit.scalar_vector_mul(ai, glevi) for ai, glevi in zip(a_decomp, glev)]
        return Circuit.add_vec_n(vecs)
    
    def test_glev_inner(n=64, ks_ell=2):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=True)
        element_gate = Inp()
        glev_gates = [[Inp() for _ in range(n + 1)] for _ in range(ks_ell)]
        out_gates = circuit.glev_inner(element_gate, glev_gates, ks_ell)
        circuit.add_out_gates(out_gates)
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(sum(glev_gates, [element_gate]))
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
        print(f"Plonk parameter d and d_max: {plonk.d}, {plonk.d_max}")
        
        V = VectorSpace(F, n + 1)
        glev = [V.random_element() for _ in range(ks_ell)]
        
        inp = {element_gate.gid : F.random_element()}
        for ct, gate in zip(glev, glev_gates):
            inp.update({g.gid : vi for vi, g in zip(ct, gate)})
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def key_switch(self, lwe_ct, ksk):
        ks_ell = len(ksk[0])
        vecs = [self.glev_inner(ai, glev, ks_ell) for ai, glev in zip(lwe_ct[:-1], ksk)]
        vec = Circuit.add_vec_n(vecs)
        fst = [self.get_constant_gate(0) for _ in vec[:-1]] + [lwe_ct[-1]]
        return [Add(fi, self.neg_gate(vi)) for fi, vi in zip(fst, vec)]

    def test_ks(n0=8, n1=4, ks_ell=2):
        plonk = Circuit.setup()
        F = plonk.P.base_ring()
        circuit = Circuit(F, [], plookup=True)
        lwe_gates = [Inp() for _ in range(n0 + 1)]
        ksk_gates = [[[Inp() for _ in range(n1 + 1)] for _ in range(ks_ell)] for _ in range(n0)]
        out_gates = circuit.key_switch(lwe_gates, ksk_gates)
        
        circuit.add_out_gates(out_gates)
        circuit.assign_gids()
        
        print("Generating circuit data")
        circuit_data = circuit.generate_circuit_data(sum([sum(gates, []) for gates in ksk_gates], lwe_gates))
        pinput, vinput = plonk.preprocess_circuit(*circuit_data)
        print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
        print(f"Plonk parameter d and d_max: {plonk.d}, {plonk.d_max}")
        
        lwe_ct = vector([F.random_element() for _ in range(n0 + 1)])
        
        V = VectorSpace(F, n1 + 1)
        ksk = [[V.random_element() for _ in range(ks_ell)] for _ in range(n0)]
        
        inp = {g.gid : vi for g, vi in zip(lwe_gates, lwe_ct)}
        for glev_gate, glev in zip(ksk_gates, ksk):
            for gate, vec in zip(glev_gate, glev):
                inp.update({g.gid : vi for vi, g in zip(vec, gate)})
        
        print("Generating trace data")
        trace_data = circuit.get_trace(inp)
        
        prf = plonk.prove(pinput, *trace_data)
        assert plonk.verify(vinput, prf)
    
    def test_all():
        Circuit.test_basic()
        Circuit.test_neg()
        Circuit.test_zero_test()
        Circuit.test_range()
        
        # ensure decomposition base is smaller than circuit size
        Circuit.decomp_base = 16
        Circuit.decomp_ell = 16
        
        Circuit.test_decomp()
        Circuit.test_poly_decomp()
        
        Circuit.decomp_base = 256
        Circuit.decomp_ell = 8
        Circuit.test_bin_decomp()
        
        Circuit.test_add_n()
        Circuit.test_mul_n()
        Circuit.test_inner()
        Circuit.test_poly_add()
        Circuit.test_poly_add_n()
        Circuit.test_poly_mul()
        Circuit.test_poly_inner()
        Circuit.test_external_product(pbs_ell=2)
        Circuit.test_rotate_poly_const()
        Circuit.test_rotate_polys()
        Circuit.test_blind_rot_step()
        Circuit.test_blind_rot()
        
        Circuit.test_add_vec_n()
        Circuit.test_glev_inner()
        Circuit.test_ks()
        


# Circuit.test_external_product(N=8);
# Circuit.test_external_product(N=16);
# Circuit.test_external_product(N=32);
# Circuit.test_external_product(N=64);
# Circuit.test_external_product(N=128);
