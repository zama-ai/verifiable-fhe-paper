from enum import Enum

class GateType(Enum):
    MUL = 0
    ADD = 1
    INP = 2
    CNT = 3
    WTN = 4

class DecompType(Enum):
    GADGET = 0
    BINARY = 1
    NEGMOD2N = 2

class Gate:
    F = None
    decomp_base = None
    decomp_ell = None
    max_fan_in = 2
    
    def __init__(self):
        self.gid = None
        self.out_value = None
        self.decomposes_into = None
        self.decomposes = None
        self.decomp_type = DecompType.GADGET
    
    def clear(self):
        self.gid = None
        self.out_value = None
    
    def clear_trace(self):
        self.out_value = None
    
    def assign_gids(self, gstart, istart):
        raise NotImplementedError("This function should be overwritten!")
    
    def assign_wtn_gids(self, istart):
        raise NotImplementedError("This function should be overwritten!")
    
    def print_circuit(self, pre=""):
        print(pre + str(self._typ_string()))
    
    def _typ_string(self):
        raise NotImplementedError("This function should be overwritten!")
    
    def get_selector(self, typ):
        raise NotImplementedError("This function should be overwritten!")
    
    def get_trace(self, inp):
        raise NotImplementedError("This function should be overwritten!")
    
    def _out_wire(self):
        raise NotImplementedError("This function should be overwritten!")
    
    def _in_wires(self):
        raise NotImplementedError("This function should be overwritten!")
    
    def _empty_wires(self):
        raise NotImplementedError("This function should be overwritten!")
    
    def get_wires(self):
        raise NotImplementedError("This function should be overwritten!")
    
    def collect_empty_wires(self):
        return self._empty_wires()
    
    def plonk_columns():
        return Gate.max_fan_in + 1
    
    def _gadget_decompose(value):
        a = value.lift_centered()
        B = Gate.decomp_base
        sgn = 1 if a >= 0 else -1
        a *= sgn
        decomp = []
        for i in range(Gate.decomp_ell):
            t = a % B
            a -= t
            a /= B
            if t > B / 2:
                t -= B
                a += 1
            decomp.append(Gate.F(sgn * t))
        return decomp
    
    def _decompose(self):
        if self.out_value == None:
            raise ValueError(f"Out value needs to be computed before evaluating decomposition. {self.decomp_type}")
        if self.decomposes_into:
            if self.decomp_type == DecompType.GADGET:
                # perform gadget decomposition
                for gate, val in zip(self.decomposes_into, Gate._gadget_decompose(self.out_value)):
                    gate.out_value = val
            elif self.decomp_type == DecompType.BINARY:
                nbits = len(self.decomposes_into)
                a = self.out_value.lift()
                bits = a.digits(2, padto=nbits)
                for bit, gate in zip(bits, self.decomposes_into):
                    gate.out_value = self.F(bit)
            elif self.decomp_type == DecompType.NEGMOD2N:
                self.decomposes_into.out_value = Gate.F(1) if self.out_value else Gate.F(0)
            else:
                raise ValueError("Unknown decomposition type")
    def _insert_append(dct, key, value):
        if not key in dct:
            dct[key] = value
        else:
            dct[key] += value

class Arithmetic(Gate):
    def __init__(self):
        raise ValueError("Arithmetic gate requires inputs left and right.")
    
    def __init__(self, left, right):
        Gate.__init__(self)
        self.left = left
        self.right = right
        self.wires_collected = False
        self.empty_wires_collected = False
        self.selector_collected = {GateType.ADD : False, GateType.MUL : False, GateType.CNT : False}
    
    def clear(self):
        Gate.clear(self)
        self.left.clear();
        self.right.clear();
        
        self.wires_collected = False
        self.empty_wires_collected = False
        self.selector_collected = {GateType.ADD : False, GateType.MUL : False, GateType.CNT : False}
    
    def clear_trace(self):
        Gate.clear_trace(self)
        self.left.clear_trace();
        self.right.clear_trace();
    
    def assign_gids(self, gstart, istart):
        if self.gid == None:
            gstart, istart = self.left.assign_gids(gstart, istart)
            gstart, istart = self.right.assign_gids(gstart, istart)
            
            self.gid = gstart
            gstart += 1
        
        return gstart, istart
    
    def assign_wtn_gids(self, istart):
        istart = self.left.assign_wtn_gids(istart)
        istart = self.right.assign_wtn_gids(istart)
        return istart
    
    def print_circuit(self, pre=""):
        self.left.print_circuit(pre + " ")
        self.right.print_circuit(pre + " ")
        Gate.print_circuit(self, pre)
    
    def get_selector(self, typ):
        if self.selector_collected[typ]:
            return {}
        selector = {self.gid : self._get_selector_value(typ)}
        
        selector.update(self.left.get_selector(typ))
        selector.update(self.right.get_selector(typ))
        
        self.selector_collected[typ] = True
        return selector
    
    def _get_selector_value(self, typ):
        raise NotImplementedError("This function should be overwritten!")
    
    def _gate_result(self, a, b):
        raise NotImplementedError("This function should be overwritten!")
    
    def get_trace(self, inp):
        if self.out_value != None:
            # already visited
            return {}, {}
        
        trace, witnesses = self.left.get_trace(inp)
        t_r, w_r = self.right.get_trace(inp)
        trace.update(t_r)
        witnesses.update(w_r)
        
        l_out = self.left.out_value
        r_out = self.right.out_value
        out = self._gate_result(l_out, r_out)
    
        self.out_value = out
    
        if self.gid in trace:
            raise ValueError(f"Duplicate gid {self.gid}. This should not happen.")
            
        trace[self.gid] = tuple([l_out, r_out, out] + [0] * (Gate.plonk_columns() - 3))
        
        self._decompose()
        
        return trace, witnesses
    
    def _out_wire(self):
        return Gate.plonk_columns() * self.gid + 2
    
    def _in_wires(self):
        return (Gate.plonk_columns() * self.gid, Gate.plonk_columns() * self.gid + 1)
    
    def _empty_wires(self):
        return list(range(Gate.plonk_columns() * self.gid + 3, Gate.plonk_columns() * (self.gid + 1)))
    
    def _insert_append(dct, key, value):
        if not key in dct:
            dct[key] = value
        else:
            dct[key] += value
    
    def get_wires(self):
        if self.wires_collected:
            return {}
        wires = {}
        in_wires = self._in_wires()
        Gate._insert_append(wires, self.left._out_wire(), [in_wires[0]])
        Gate._insert_append(wires, self.right._out_wire(), [in_wires[1]])
        
        for out_wire, in_wires in self.left.get_wires().items():
            Gate._insert_append(wires, out_wire, in_wires)
        
        for out_wire, in_wires in self.right.get_wires().items():
            Gate._insert_append(wires, out_wire, in_wires)
        
        self.wires_collected = True
        return wires
    
    def collect_empty_wires(self):
        if self.empty_wires_collected:
            return []
        empty_wires = self.left.collect_empty_wires()
        empty_wires += self.right.collect_empty_wires()
        empty_wires += Gate.collect_empty_wires(self)
        
        self.empty_wires_collected = True
        
        return empty_wires
    
class Add(Arithmetic):
    def _typ_string(self):
        return f"add gate #{self.gid}"
    
    def _gate_result(self, a, b):
        return a + b
    
    def _get_selector_value(self, typ):
        return 1 if typ == GateType.ADD else 0

class Mul(Arithmetic):
    def _typ_string(self):
        return f"mul gate #{self.gid}"
    
    def _gate_result(self, a, b):
        return a * b
    
    def _get_selector_value(self, typ):
        return 1 if typ == GateType.MUL else 0

class Inp(Gate):
    def assign_gids(self, gstart, istart):
        if self.gid == None:
            self.gid = istart
            istart -= 1
        
        return gstart, istart
    
    def assign_wtn_gids(self, istart):
        return istart
    
    def _typ_string(self):
        return f"input #{self.gid}"
    
    def get_selector(self, typ):
        return {}
    
    def get_trace(self, inp):
        if self.out_value != None:
            # already visited
            return {}, {}
        
        self.out_value = inp[self.gid]
        
        self._decompose()
        
        return {}, {}
    
    def _out_wire(self):
        return self.gid
    
    def _in_wires(self):
        print("Warning: No in wires to input gates")
        return None
    
    def _empty_wires(self):
        return []
    
    def get_wires(self):
        return {}

class Cnt(Gate):
    def __init__(self):
        raise ValueError("Constant gates require a constant.")
    
    def __init__(self, constant):
        Gate.__init__(self)
        self.constant = Gate.F(constant)
    
    def assign_gids(self, gstart, istart):        
        if self.gid == None:
            self.gid = gstart
            gstart += 1
        
        return gstart, istart
    
    def assign_wtn_gids(self, istart):
        return istart
    
    def _typ_string(self):
        return f"constant #{self.gid}"
    
    def get_selector(self, typ):
        return {self.gid : self.constant if typ == GateType.CNT else 0}
    
    def get_trace(self, inp):
        if self.out_value != None:
            # already visited
            return {}, {}
        
        self.out_value = self.constant
        trace = {self.gid : tuple([0, 0, self.constant] + [0] * (Gate.plonk_columns() - 3))}
        
        self._decompose()
        
        return trace, {}
    
    def _out_wire(self):
        return Gate.plonk_columns() * self.gid + 2
    
    def _in_wires(self):
        return (Gate.plonk_columns() * self.gid, Gate.plonk_columns() * self.gid + 1)
    
    def _empty_wires(self):
        empty = list(range(Gate.plonk_columns() * self.gid + 3, Gate.plonk_columns() * (self.gid + 1)))
        empty += list(self._in_wires())
        return empty
    
    def get_wires(self):
        return {}

class Wtn(Gate):
    def assign_gids(self, gstart, istart):
        # we skip witness gates during gid assignment and do them extra, see below
        return gstart, istart
    
    def assign_wtn_gids(self, istart):
        if self.gid == None:
            self.gid = istart
            istart -= 1
        return istart
    
    def _typ_string(self):
        f"witness #{self.gid}"
    
    def get_selector(self, typ):
        return {}
    
    def get_trace(self, inp):
        if not self.decomposes:
            raise ValueError("Witness that does not decompose another value. Cannot compute its value.")
        
        trace, witnesses = self.decomposes.get_trace(inp)
        witnesses[self.gid] = self.out_value
        self._decompose()
        
        return trace, witnesses
    
    def _out_wire(self):
        return self.gid
    
    def _in_wires(self):
        print("Warning: No in wires to witness gates")
        return None
    
    def _empty_wires(self):
        return []
    
    def get_wires(self):
        return {}
