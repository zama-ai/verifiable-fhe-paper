# WARNING: outdated.

load("circuit.sage")

n = 3
pmod = 4
k = 1
N = 8
pbs_ell = 2

Z2N = Integers(2 * N)
R.<y> = P.quotient(x^N + 1)

def lwe_keygen(n):
    return [randint(0, 1) for _ in range(n)]

def lwe_enc(s, m):
    mask = [randint(0, 2*N - 1) for _ in s]
    return mask + [(vector(Z2N, mask) * vector(Z2N, s) + m * (2 * N // pmod)).lift()]

def lwe_dec(s, c):
    mask = c[:-1]
    body = c[-1]
    return (Z2N(body) - vector(Z2N, mask) * vector(Z2N, s)).lift() * pmod // (2 * N)

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

# set up the circuit
circuit = Circuit([], plookup=True)
testv_gates = [Inp() for _ in range(N)]
lwe_ct_gates = [Inp() for _ in range(n + 1)]
bsk_gates = [GGswGates(k, N, pbs_ell) for _ in range(n)]

out_gates = circuit.blind_rot(testv_gates, lwe_ct_gates, bsk_gates, pbs_ell)
circuit.add_out_gates(sum(out_gates, []))
circuit.assign_gids()
print("Generating circuit data")
circuit_data = circuit.generate_circuit_data(testv_gates + lwe_ct_gates + sum([ggsw.flatten() for ggsw in bsk_gates], []))
print(f"Circuit size: {len(circuit_data[0][0])}")
