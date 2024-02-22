# WARNING: outdated.

# generate inputs

s_lwe = lwe_keygen(n)
m = randint(0, pmod - 1)
lwe_ct = lwe_enc(s_lwe, m)

Delta = p // 4
testv = R([Delta for _ in range(N)])

s_glwe = glwe_keygen(k)
bsk = compute_bsk(s_glwe, s_lwe)


print(f"s_lwe: {s_lwe}")
print(f"s_glwe: {s_glwe}")
print(f"lwe_ct: {lwe_ct}")

# set the input

inp = Circuit.set_poly_inp(testv_gates, testv)
for i, bsk_gate, bsk_input in zip(range(len(bsk)), bsk_gates, bsk):
    inp.update(bsk_gate.set_input(bsk_input, ntt=True))


for lwe_in_gate, lwe_input in zip(lwe_ct_gates, lwe_ct):
    inp[lwe_in_gate.gid] = F(lwe_input)

# do the computation
trace_data = circuit.get_trace(inp)
print("Trace computed")

# store the result
glwe_ct = [R([gate.out_value for gate in out_gate]) for out_gate in out_gates]

plonk_data = tuple(list(trace_data) + list(circuit_data))

# prove the computation
t = cputime()
prf = plonkify(*plonk_data)
print(f"Generated plonk proof in {cputime(t)}s.")
print(f"Proof size: {plonk_proof_size(prf)} hash values and field elements")

# verify the result
assert verify_plonk(prf)
    
m_ = glwe_dec(s_glwe, glwe_ct)
print(f"in m={m}, out m={0 if m_[0].lift_centered() >= 0 else 1}")
