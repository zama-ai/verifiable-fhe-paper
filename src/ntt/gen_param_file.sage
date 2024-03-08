import sys

def compute_params(N, q, inv2, prim_root, inv_prim_root):
    e = (q - 1) // (2 * N)
    w = power_mod(prim_root, e, q)
    w_inv = power_mod(inv_prim_root, e, q)
    roots = [power_mod(w, j, q) for j in range(N)]
    roots_inv = [power_mod(w_inv, j, q) for j in range(N)]
    n_inv = power_mod(inv2, N.log(2), q)
    return roots, roots_inv, n_inv


# ~ def ntt_trivial_forward(q, N, roots, poly_in):
    # ~ R = poly_in.parent()
    # ~ a = []
    
    # ~ for i in range(N):
        # ~ wi = [power_mod(roots[i], j, q) for j in range(N)]
        # ~ aw = [mod(wij * pj, q) for wij, pj in zip(wi, poly_in)]
        # ~ a.append(sum(aw))
    
    # ~ return R(a)

# ~ def ntt_trivial_backward(q, N, roots_inv, n_inv, poly_in):
    # ~ R = poly_in.parent()
    # ~ a = []
    
    # ~ for i in range(N):
        # ~ wi = [power_mod(roots_inv[i], j, q) for j in range(N)]
        # ~ aw = [mod(wij * pj, q) for wij, pj in zip(wi, poly_in)]
        # ~ a.append(n_inv * sum(aw))
    # ~ return R(a)

def ntt_forward(q, N, roots, poly_in):
    logN = log(N, 2)
        
    twiddles = bit_reverse(roots)
        
    a = [list(poly_in)]
    t = N
    for m in [2^i for i in range(logN)]:
        a_out = [None for _ in range(N)]
        t /= 2
        for i in range(m):
            j1 = 2 * i * t
            j2 = j1 + t - 1
            S = twiddles[m + i]
            for j in range(j1, j2 + 1):
                U = a[-1][j]
                V = a[-1][j + t] * S
                a_out[j] = U + V
                a_out[j + t] = U - V
        # ~ print(a_out)
        a.append(a_out)
    return a[-1]

def ntt_backward(q, N, Ninv, roots_inv, poly_in):
    logN = log(N, 2)
    
    twiddles = bit_reverse(roots_inv)
    
    a = [list(poly_in)]
    t = 1
    for m in [2^i for i in range(1, logN + 1)][::-1]:
        a_out = [None for _ in range(N)]
        j1 = 0
        h = m / 2
        for i in range(h):
            j2 = j1 + t - 1
            S = twiddles[h + i]
            for j in range(j1, j2 + 1):
                U = a[-1][j]
                V = a[-1][j + t]
                a_out[j] = U + V
                diff = U - V
                a_out[j + t] = diff * S
            j1 += 2 * t
        t *= 2
        a.append(a_out)
    
    return [Ninv * ai for ai in a[-1]]

def bit_reverse_index(index, log_size):
    return int(bin(index)[2:][::-1].ljust(log_size, '0'), 2)

def bit_reverse(lst):
    log_size = int(log(len(lst), 2))
    return [lst[bit_reverse_index(j, log_size)] for j in range(len(lst))]

def compute_init_params(q):
    inv2 = inverse_mod(2, q)
    
    prim_root = primitive_root(q)
    inv_prim_root = inverse_mod(prim_root, q)
    return inv2, prim_root, inv_prim_root

def gen_param_file(q, N, namef="params_{0}.rs"):
    inv2, prim_root, inv_prim_root = compute_init_params(q)
    roots, roots_inv, n_inv = compute_params(N, q, inv2, prim_root, inv_prim_root)
    P.<x> = PolynomialRing(Integers(q))
    g = P.random_element(N - 1)
    # ~ ghat = ntt_trivial_forward(q, N, roots, g)
    ghat = ntt_forward(q, N, roots, g)
    # ~ print(list(ghat))
    # ~ print(list(ghat) == ghat_)
    # ~ g_ = ntt_backward(q, N, n_inv, roots_inv, ghat)
    # ~ print(g == P(g_))
    with open(namef.format(N), 'w') as f:
        f.write(f"pub const N: usize = {N};\n")
        f.write(f"pub const LOGN: u32 = {log(N, 2)};\n")
        f.write(f"pub const NINV: u64 = {n_inv};\n\n")
        f.write(f"pub const ROOTS: [u64; {N}] = {bit_reverse(roots)};\n\n")
        f.write(f"pub const INVROOTS: [u64; {N}] = {bit_reverse(roots_inv)};\n\n")
        f.write("// Test Vectors\n\n")
        f.write(f"pub const TESTG: [u64; {N}] = {list(g)};\n\n")
        f.write(f"pub const TESTGHAT: [u64; {N}] = {ghat};\n\n")
        
q = 2^64 - 2^32 + 1
N = ZZ(sys.argv[1])
gen_param_file(q, N)
