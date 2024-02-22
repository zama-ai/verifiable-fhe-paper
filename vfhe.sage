load("circuit.sage")

n = 4
pmod = 4
k = 1
N = 8
pbs_ell = 2
ksk_ell = 2

plonk = Circuit.setup()
R.<y> = plonk.P.quotient(x^N + 1)
F = plonk.P.base_ring()
q = F.order()

def lwe_keygen(n):
    return [randint(0, 1) for _ in range(n)]

def lwe_enc(s, m):
    mask = [F.random_element() for _ in s]
    return mask + [vector(F, mask) * vector(F, s) + F(m * (q // pmod))]

def lwe_dec(s, c):
    mask = c[:-1]
    body = c[-1]
    m_ = body - vector(F, mask) * vector(F, s)
    
    return (m_ + q // (2 * pmod)).lift() * pmod // q

def glwe_keygen(k):
    return vector(R, [[randint(0, 1) for _ in range(N)] for _ in range(k)])

def glwe_enc(s, m, ntt=False):
    mask = vector([R.random_element() for _ in s])
    body = m + mask * s
    
    if ntt:
        mask = mask.apply_map(Circuit._compute_ntt_fw)
        body = Circuit._compute_ntt_fw(body)
    return list(mask) + [body]

def glwe_dec(s, c):
    mask = vector(c[:-1])
    body = c[-1]
    return body - mask * s

def glev(s, m, ntt=False):
    return [glwe_enc(s, b * m) for b in [Circuit.decomp_base^i for i in range(Circuit.decomp_ell - pbs_ell, Circuit.decomp_ell)]]

def ggsw_enc(s, m, ntt=False):
    return [glev(s, si * m) for si in s] + [glev(s, m)]

def compute_bsk(s_glwe, s_lwe):
    return [ggsw_enc(s_glwe, si) for si in s_lwe]

def compute_ksk(s1, s2):
    ksk = []
    for si in s2:
        glev = []
        for b in [Circuit.decomp_base^i for i in range(Circuit.decomp_ell - ksk_ell, Circuit.decomp_ell)]:
            mask = [F.random_element() for _ in s1]
            glev.append(mask + [vector(mask) * vector(F, s1) + F(si * b)])
        ksk.append(glev)
    return ksk

def decomp_poly(poly):
    m = matrix(F, [Gate._gadget_decompose(a) for a in poly])
    return [R(list(a)) for a in m.transpose()][-pbs_ell:]

def glev_mul(poly, glev_ct):
    small_polys = vector(R, decomp_poly(poly))
    base_vector = [Circuit.decomp_base^i for i in range(Circuit.decomp_ell - pbs_ell, Circuit.decomp_ell)]
    test_poly = sum([b * p for b, p in zip(base_vector, small_polys)])
    return small_polys * matrix(R, glev_ct)

def x_prod(glwe_ct, ggsw_ct):
    return glev_mul(glwe_ct[-1], ggsw_ct[-1]) - sum([glev_mul(glwe, ggsw) for glwe, ggsw in zip(glwe_ct[:-1], ggsw_ct[:-1])])

def cmux(glwe_ct0, glwe_ct1, ggsw_ct):
    return x_prod(glwe_ct1 - glwe_ct0, ggsw_ct) + glwe_ct0

def mod_switch(lwe_element):
    logN = int(round(log(N, 2)))
    return ZZ(lwe_element.lift().binary().rjust(64, '0')[:logN + 1], 2)

def blind_rot_step(glwe_ct, ggsw_ct, lwe_element):
    ct = vector(glwe_ct)
    return cmux(ct, y^mod_switch(lwe_element) * ct, ggsw_ct)

def blind_rot(testv, bsk, lwe_ct):
    glwe_ct = vector(R, [0] * k + [testv * y^(mod_switch(-lwe_ct[-1]))])
    for ggsw_ct, lwe_element in zip(bsk, lwe_ct[:-1]):
        glwe_ct = blind_rot_step(glwe_ct, ggsw_ct, lwe_element)
    
    return glwe_ct

def key_switch(lwe_ct, ksk):
    n = len(ksk[0][0]) - 1
    acc = vector(F, [0] * n + [lwe_ct[-1]])
    for a, glev in zip(lwe_ct[:-1], ksk):
        a_decomp = Gate._gadget_decompose(a)[-ksk_ell:]
        for ai, ct in zip(a_decomp, glev):
            acc -= ai * vector(F, ct)
    return list(acc)

def v_glev_mul():
    circuit = Circuit(F, [], plookup=True, N=N)
    
    glwe_in_gates = PolyGates(N)
    glev_in_gates = GLevGates(k, N, pbs_ell)
    
    out_gates = circuit.glev_mul(glwe_in_gates.gates, glev_in_gates, pbs_ell)
    circuit.add_out_gates(sum(out_gates, []))
    circuit.assign_gids()
    
    print("Generating circuit data")
    circuit_data = circuit.generate_circuit_data(glwe_in_gates.gates + glev_in_gates.flatten())
    pinput, vinput = plonk.preprocess_circuit(*circuit_data)
    print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
    
    s_glwe = glwe_keygen(k)
    poly = R.random_element()
    m = R([randint(0, 1) for _ in range(N)])
    glev_ct = glev(s_glwe, m)
    
    inp = glwe_in_gates.set_input(poly)
    
    inp.update(glev_in_gates.set_input(glev_ct, ntt=True))
    
    print("Generating trace data")
    trace_data = circuit.get_trace(inp)
    print("trace computed. Checking result.")
    
    expected = glev_mul(poly, glev_ct)
    actual = [R(list(glwe_in_gates._compute_ntt_bw(R([gate.out_value for gate in out_gate])))) for out_gate in out_gates]
    
    for ac, ex in zip(actual, expected):
        assert ac == ex, "glev mul result doesn't match"
    
    t = cputime()
    prf = plonk.prove(pinput, *trace_data)
    print(f"Generated plonk proof in {cputime(t)}s.")
    print(f"Proof size: {plonk.proof_size(prf)} hash values and field elements")
    assert plonk.verify(vinput, prf)

def v_x_prod():
    circuit = Circuit(F, [], plookup=True, N=N)
    glwe_in_gates = GLweGates(k, N)
    ggsw_in_gates = GGswGates(k, N, pbs_ell)
    
    out_gates = circuit.external_product(glwe_in_gates.to_lists(), ggsw_in_gates, pbs_ell)
    circuit.add_out_gates(sum(out_gates, []))
    circuit.assign_gids()
    print("Generating circuit data")
    circuit_data = circuit.generate_circuit_data(glwe_in_gates.flatten() + ggsw_in_gates.flatten())
    pinput, vinput = plonk.preprocess_circuit(*circuit_data)
    print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
    
    s_glwe = glwe_keygen(k)
    m = R.random_element()
    glwe_inputs = glwe_enc(s_glwe, m)
    
    b = randint(0, 1)
    print(b)
    ggsw_inputs = ggsw_enc(s_glwe, b)
    
    inp = glwe_in_gates.set_input(glwe_inputs)
    inp.update(ggsw_in_gates.set_input(ggsw_inputs, ntt=True))
    print("Generating trace data")
    trace_data = circuit.get_trace(inp)
    
    expected = x_prod(glwe_inputs, ggsw_inputs)
    actual = [R([gate.out_value for gate in out_gate]) for out_gate in out_gates]
    
    for ac, ex in zip(actual, expected):
        assert ac == ex, "external products don't match"
    
    # this is only a meaningful test for exact decomposition or some proper encoding
    # ~ assert b * m == glwe_dec(s_glwe, actual), "decrypted incorrect result."
    
    t = cputime()
    prf = plonk.prove(pinput, *trace_data)
    print(f"Generated plonk proof in {cputime(t)}s.")
    print(f"Proof size: {plonk.proof_size(prf)} hash values and field elements")

    assert plonk.verify(vinput, prf)

def v_blind_rot_step():
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
    print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
    
    s_glwe = glwe_keygen(k)
    m = R.random_element()
    glwe_inputs = glwe_enc(s_glwe, m)
    
    b = randint(0, 1)
    print(b)
    ggsw_inputs = ggsw_enc(s_glwe, b)

    
    lwe_input = F.random_element()
    
    inp = glwe_in_gates.set_input(glwe_inputs)
    inp.update(ggsw_in_gates.set_input(ggsw_inputs, ntt=True))
    inp[lwe_in_gate.gid] = F(lwe_input)
    
    print("Generating trace data")
    trace_data = circuit.get_trace(inp)
    
    expected = blind_rot_step(glwe_inputs, ggsw_inputs, lwe_input)
    actual = [R([gate.out_value for gate in out_gate]) for out_gate in out_gates]
    
    for ac, ex in zip(actual, expected):
        assert ac == ex, "blind rotation step doesn't match"
    
    # ~ assert glwe_dec(s_glwe, actual) ==  m * y^(b * lwe_input), "blind rot step: decrypted incorrect result"
    
    t = cputime()
    prf = plonk.prove(pinput, *trace_data)
    print(f"Generated plonk proof in {cputime(t)}s.")
    print(f"Proof size: {plonk.proof_size(prf)} hash values and field elements")
    assert plonk.verify(vinput, prf)

def verifiable_blind_rotation():
    # set up the circuit
    circuit = Circuit(F, [], plookup=True, N=N)
    testv_gates = PolyGates(N)
    lwe_ct_gates = [Inp() for _ in range(n + 1)]
    bsk_gates = [GGswGates(k, N, pbs_ell) for _ in range(n)]
    
    out_gates = circuit.blind_rot(testv_gates.gates, lwe_ct_gates, bsk_gates, pbs_ell)
    circuit.add_out_gates(sum(out_gates, []))
    circuit.assign_gids()
    print("Generating circuit data")
    circuit_data = circuit.generate_circuit_data(testv_gates.gates + lwe_ct_gates + sum([ggsw.flatten() for ggsw in bsk_gates], []))
    pinput, vinput = plonk.preprocess_circuit(*circuit_data)
    print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
    
    # compute inputs
    s_lwe = lwe_keygen(n)
    print(f"s_lwe: {s_lwe}")
    Delta = p // 4
    testv = R([Delta for _ in range(N)])
    s_glwe = glwe_keygen(k)
    bsk = compute_bsk(s_glwe, s_lwe)
    print(f"s_glwe: {s_glwe}")
    # set the input
    inp = testv_gates.set_input(testv)
    print("test vector assigned")
    for i, bsk_gate, bsk_input in zip(range(len(bsk)), bsk_gates, bsk):
        inp.update(bsk_gate.set_input(bsk_input, ntt=True))
    print("bsk assigned")
    
    glwe_cts = []
    prfs = []
    for m in range(pmod):
        lwe_ct = lwe_enc(s_lwe, m)
        
        print(f"lwe_ct: {lwe_ct}")
        
        for lwe_in_gate, lwe_input in zip(lwe_ct_gates, lwe_ct):
            inp[lwe_in_gate.gid] = F(lwe_input)
        
        print("Inputs assigned")
        
        # do the computation
        trace_data = circuit.get_trace(inp)
        print("Trace computed")
        
        # store the result
        glwe_cts.append([R([gate.out_value for gate in out_gate]) for out_gate in out_gates])
        
        # check the result
        expected = blind_rot(testv, bsk, lwe_ct)
        actual = [R([gate.out_value for gate in out_gate]) for out_gate in out_gates]
        
        for ac, ex in zip(actual, expected):
            assert ac == ex
        
        # prove the computation
        t = cputime()
        prfs.append(plonk.prove(pinput, *trace_data))
        print(f"Generated plonk proof in {cputime(t)}s.")
        print(f"Proof size: {plonk.proof_size(prfs[-1])} hash values and field elements")
        circuit.clear_trace()
    
    for m, glwe_ct, prf in zip(range(pmod), glwe_cts, prfs):
        # verify the result
        assert plonk.verify(vinput, prf)
        
        m_ = glwe_dec(s_glwe, glwe_ct)
        print(f"in m={m}, out m={0 if m_[0].lift_centered() >= 0 else 1}")

def verifiable_key_switch():
    plonk = Circuit.setup()
    F = plonk.P.base_ring()
    circuit = Circuit(F, [], plookup=True)
    n = 8
    k = 2
    lwe_gates = [Inp() for _ in range(n + 1)]
    ksk_gates = [[[Inp() for _ in range(N * k + 1)] for _ in range(ksk_ell)] for _ in range(n)]
    out_gates = circuit.key_switch(lwe_gates, ksk_gates)
    
    circuit.add_out_gates(out_gates)
    circuit.assign_gids()
    
    print("Generating circuit data")
    circuit_data = circuit.generate_circuit_data(sum([sum(gates, []) for gates in ksk_gates], lwe_gates))
    pinput, vinput = plonk.preprocess_circuit(*circuit_data)
    print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
    print(f"Plonk parameter d and d_max: {plonk.d}, {plonk.d_max}")
    
    # compute inputs
    s_lwe = lwe_keygen(n)
    print(f"s_lwe: {s_lwe}")
    s_glwe = glwe_keygen(k)
    print(f"s_glwe: {s_glwe}")
    s_glwe_ = sum([list(si) for si in s_glwe], [])
    ksk = compute_ksk(s_glwe_, s_lwe)
    m = randint(0, pmod - 1)
    lwe_ct = lwe_enc(s_lwe, m)
    print(f"m: {m}, lwe_ct: {lwe_ct}")
    
    lwe_ct_ = key_switch(lwe_ct, ksk)
    
    assert lwe_dec(s_glwe_, lwe_ct_) == m
    
    inp = {g.gid : vi for g, vi in zip(lwe_gates, lwe_ct)}
    for glev_gate, glev in zip(ksk_gates, ksk):
        for gate, vec in zip(glev_gate, glev):
            inp.update({g.gid : vi for vi, g in zip(vec, gate)})
    
    print("Generating trace data")
    trace_data = circuit.get_trace(inp)
    
    lwe_ct_out = [gate.out_value for gate in out_gates]
    assert vector(F, lwe_ct_) == vector(F, lwe_ct_out)
    
    prf = plonk.prove(pinput, *trace_data)
    assert plonk.verify(vinput, prf)

def verifiable_pbs():
    # set up the circuit
    circuit = Circuit(F, [], plookup=True, N=N)
    testv_gates = PolyGates(N)
    lwe_ct_gates = [Inp() for _ in range(n + 1)]
    bsk_gates = [GGswGates(k, N, pbs_ell) for _ in range(n)]
    ksk_gates = [[[Inp() for _ in range(n + 1)] for _ in range(ksk_ell)] for _ in range(N * k)]
    
    br_out = circuit.blind_rot(testv_gates.gates, lwe_ct_gates, bsk_gates, pbs_ell)
    se_out = circuit.sample_extract(br_out)
    out_gates = circuit.key_switch(se_out, ksk_gates)
    
    circuit.add_out_gates(out_gates)
    circuit.assign_gids()
    print("Generating circuit data")
    input_gates = testv_gates.gates + lwe_ct_gates
    input_gates += sum([ggsw.flatten() for ggsw in bsk_gates], [])
    input_gates += sum([sum(gates, []) for gates in ksk_gates], [])
    circuit_data = circuit.generate_circuit_data(input_gates)
    pinput, vinput = plonk.preprocess_circuit(*circuit_data)
    print(f"Circuit data generated. Parameters (C, I, W) = {circuit_data[:3]}. Ready to plonk.")
    
    # compute inputs
    s_lwe = lwe_keygen(n)
    print(f"s_lwe: {s_lwe}")
    Delta = F(q // 4)
    testv = R([Delta for _ in range(N)])
    s_glwe = glwe_keygen(k)
    bsk = compute_bsk(s_glwe, s_lwe)
    s_glwe_ = sum([list(si) for si in s_glwe], [])
    ksk = compute_ksk(s_lwe, s_glwe_)
    print(f"s_glwe: {s_glwe}")
    
    # set the input
    inp = testv_gates.set_input(testv)
    print("test vector assigned")
    for i, bsk_gate, bsk_input in zip(range(len(bsk)), bsk_gates, bsk):
        inp.update(bsk_gate.set_input(bsk_input, ntt=True))
    print("bsk assigned")
    
    for glev_gate, glev in zip(ksk_gates, ksk):
        for gate, vec in zip(glev_gate, glev):
            inp.update({g.gid : vi for vi, g in zip(vec, gate)})
    
    out_cts = []
    prfs = []
    for m in range(pmod):
        lwe_ct = lwe_enc(s_lwe, m)
        print(f"lwe_ct: {lwe_ct}")
        
        for lwe_in_gate, lwe_input in zip(lwe_ct_gates, lwe_ct):
            inp[lwe_in_gate.gid] = F(lwe_input)
        
        print("Inputs assigned")
        
        # do the computation
        trace_data = circuit.get_trace(inp)
        print("Trace computed")
        
        out_cts.append([gate.out_value for gate in out_gates])
        
        
        # prove the computation
        t = cputime()
        prf = plonk.prove(pinput, *trace_data)
        prfs.append(prf)
        print(f"Generated plonk proof in {cputime(t)}s.")
        print(f"Proof size: {plonk.proof_size(prf)} hash values and field elements")
        circuit.clear_trace()
    
    # verify the result
    for m, ct, prf in zip(range(pmod), out_cts, prfs):
        assert plonk.verify(vinput, prf)
        print(f"in m={m}, out m={lwe_dec(s_lwe, ct)}")
