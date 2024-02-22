# Poly commitment scheme based on FRI
import functools

load("poly_fri.sage")

### PLONK utility functions

# prove that fpol = gpol1 * gpol2
def prove_poly_product(fpol, gpol1, gpol2, h=None):
    if not h:
        h = Hash(F)
    polys = [fpol, gpol1, gpol2]
    cmts = [poly_commit(pol) for pol in polys]
    
    h.update(cmts)
    r = h.digest()
    
    prfs = [poly_open(pol, r, h) for pol in polys]
    
    return cmts, prfs

def verify_poly_product(cmts, ks, prfs, h=None):
    if not prfs[0][0] == prfs[1][0] * prfs[2][0]:
        print("poly values don't match.")
        return False
    
    if not h:
        h = Hash(F)
    
    h.update(cmts)
    r = h.digest()
    
    for cmt, k, prf in zip(cmts, ks, prfs):
        if not poly_verify(cmt, k, r, prf[0], prf[1], h):
            print("poly verification failed.")
            return False
    
    return True

def test_poly_product(iterations):
    for _ in range(iterations):
        k1 = 7
        k2 = 5
        
        g1 = P([F.random_element() for _ in range(k1)])
        g2 = P([F.random_element() for _ in range(k2)])
        
        f = g1 * g2
        cmts, prfs = prove_poly_product(vector(f), vector(g1), vector(g2))
        ks = [p.degree() + 1 for p in [f, g1, g2]]
        assert verify_poly_product(cmts, ks, prfs)

# prove that pol is 0 on {omega^i}_0^(s-1)
def prove_zero_test(pol, s, h=None):
    if not h:
        h = Hash(F)
    f = P(pol)
    q = P(f / (x^s - 1))
    
    fv = vector(f)
    qv = vector(q)
    
    f_cmt = poly_commit(fv)
    q_cmt = poly_commit(qv)
    
    h.update([f_cmt, q_cmt])
    r = h.digest()
    
    f_prf = poly_open(fv, r, h)
    q_prf = poly_open(qv, r, h)
    
    return f_cmt, q_cmt, f_prf, q_prf, len(fv), len(qv)

def verify_zero_test(prf, s, h=None):
    f_cmt, q_cmt, f_prf, q_prf, fk, qk = prf
    if not h:
        h = Hash(F)
    
    if not qk + s <= fk:
        print("zero test: invalid degree bounds.")
        return False
    
    h.update([f_cmt, q_cmt])
    r = h.digest()
    
    fr, fprf = f_prf
    qr, qprf = q_prf
    
    zr = r^s - 1
    if not fr == qr * zr:
        print("zero test failed")
    
    if not poly_verify(f_cmt, fk, r, fr, fprf, h):
        print("zero test: poly verification failed on f.")
        return False
    
    if not poly_verify(q_cmt, qk, r, qr, qprf, h):
        print("zero test: poly verification failed on q.")
        return False
    return True

def test_zero(iterations):
    for _ in range(iterations):
        s = 4
        k = 8
        om = _root_of_unity(k)
        oms = [om^i for i in range(k)]
        
        # construct a polynomial that is 0 on all powers of
        # omega^(k/s)
        vals = [F.random_element() for _ in range(k)]
        for i in range(0, len(vals), k // s):
            vals[i] = 0
        
        f = vector(F, pari.fftinv(oms, vals)) / F(k)
        fpoly = P(list(f))
        
        prf = prove_zero_test(fpoly, s)
        assert verify_zero_test(prf, s)

# prove that product of f(omega^i)/g(omega^i) for all 0 <= i < s is 1
def prove_prod_test_rational(fpol, gpol, s, h=None):
    if not h:
        h = Hash(F)
    
    f = P(fpol)
    g = P(gpol)
    
    om = _root_of_unity(s)
    oms = [om^i for i in range(s)]
    t_vals = functools.reduce(lambda x, y: x + [x[-1] * f(y) / g(y)], oms[1:], [f(oms[0]) / g(oms[0])])
    t = P(list( vector(F, pari.fftinv(oms, t_vals)) / F(s) ))
    t1 = t(om * x) * g(om * x) - t(x) * f(om * x)
    q = P(t1 / (x^s - 1))
    
    fv = vector(f)
    gv = vector(g)
    tv = vector(t)
    qv = vector(q)
    
    cmts = [poly_commit(poly) for poly in [fv, gv, tv, qv]]
    
    h.update(cmts)
    r = h.digest()
    
    t_queries = [poly_open(tv, point, h) for point in [oms[-1], r, r * om]]
    q_query = poly_open(qv, r, h)
    f_query = poly_open(fv, om * r, h)
    g_query = poly_open(gv, om * r, h)
    
    return (cmts, tuple([len(v) for v in [fv, gv, tv, qv]]), (t_queries, q_query, f_query, g_query))

def verify_prod_test_rational(prf, s, h=None):
    if not h:
        h = Hash(F)
    om = _root_of_unity(s)
    cmts, ks, queries = prf
    kf, kg, kt, kq = ks
    t_queries, q_query, f_query, g_query = queries
    
    h.update(cmts)
    r = h.digest()
    
    if not t_queries[0][0] == F(1):
        print("Product does not appear to be 1.")
        return False
    if not t_queries[2][0] * g_query[0] - t_queries[1][0] * f_query[0] == q_query[0] * (r^s - 1):
        print("Zero test on t1 failed.")
        return False
    
    f_cmt, g_cmt, t_cmt, q_cmt = cmts
    for i, query in zip([om^(s - 1), r, r * om], t_queries):
        if not poly_verify(t_cmt, kt, i, query[0], query[1], h):
            print("rational prod test: poly verification failed on t")
            return False
    
    if not poly_verify(q_cmt, kq, r, q_query[0], q_query[1], h):
        print("rational prod test: poly verification failed on q")
        return False
    
    if not poly_verify(f_cmt, kf, om * r, f_query[0], f_query[1], h):
        print("rational prod test: poly verification failed on f")
        return False
    
    if not poly_verify(g_cmt, kg, om * r, g_query[0], g_query[1], h):
        print("rational prod test: poly verification failed on f")
        return False
    return True

def test_prod_rational(iterations):
    for _ in range(iterations):
        s = 4
        k = 8
        om = _root_of_unity(k)
        oms = [om^i for i in range(k)]
        
        # construct two polynomials f and g such that the product of
        # f(omega^(i*k/s)) / g(omega^(i*k/s)) for all i is 1
        f_vals = [F.random_element() for _ in range(k)]
        g_vals = [F.random_element() for _ in range(k)]
        prd = prod([f_vals[i] for i in range(0, len(f_vals), k // s)])
        prd /= prod([g_vals[i] for i in range(k // s, len(g_vals), k // s)])
        g_vals[0] = prd
        
        f = vector(F, pari.fftinv(oms, f_vals)) / F(k)
        g = vector(F, pari.fftinv(oms, g_vals)) / F(k)
        fpoly = P(list(f))
        gpoly = P(list(g))
        
        prf = prove_prod_test_rational(fpoly, gpoly, s)
        assert verify_prod_test_rational(prf, s), "Rational prod test verification failed"

# prove that product of pol(omega^i) for all 0 <= i < s is 1
def prove_prod_test(pol, s, h=None):
    return prove_prod_test_rational(pol, P(1), s, h)
    
def verify_prod_test(prf, s, h=None):
    return verify_prod_test_rational(prf, s, h)

def test_prod(iterations):
    for _ in range(iterations):
        s = 4
        k = 8
        om = _root_of_unity(k)
        oms = [om^i for i in range(k)]
        
        # construct a polynomial f such that the product of
        # f(omega^(i*k/s)) for all i is 1
        vals = [F.random_element() for _ in range(k)]
        vals[0] = F(1) / prod([vals[i] for i in range(k // s, len(vals), k // s)])
        
        f = vector(F, pari.fftinv(oms, vals)) / F(k)
        fpoly = P(list(f))
        
        prf = prove_prod_test(fpoly, s)
        assert verify_prod_test(prf, s), "Prod test verification failed"

# prove that f(omega^i) is a permutation of g(omega^i)
def prove_permutation(fpol, gpol, s, h=None):
    if not h:
        h = Hash(F)
    
    f = P(fpol)
    g = P(gpol)
    fv = vector(f)
    gv = vector(g)
    
    cmts = [poly_commit(fv)[0], poly_commit(gv)[0]]
    h.update(cmts)
    r_ = h.digest()
    
    om = _root_of_unity(s)
    oms = [om^i for i in range(s)]
    t_vals = functools.reduce(lambda x, y: x + [x[-1] * (r_ - f(y)) / (r_ - g(y))], oms[1:], [(r_ - f(oms[0])) / (r_ - g(oms[0]))])
    
    t = P(list( vector(F, pari.fftinv(oms, t_vals)) / F(s) ))
    t1 = t(om * x) * (r_ - g(om * x)) - t(x) * (r_ - f(om * x))
    q = P(t1 / (x^s - 1))
    
    
    tv = vector(t)
    qv = vector(q)
    
    cmts_ = [poly_commit(tv)[0], poly_commit(qv)[0]]
    
    h.update(cmts_)
    r = h.digest()
    
    cmts += cmts_
    
    t_queries = [poly_open(tv, point, h=h) for point in [oms[-1], r, r * om]]
    q_query = poly_open(qv, r, h=h)
    f_query = poly_open(fv, om * r, h=h)
    g_query = poly_open(gv, om * r, h=h)
    
    return (cmts, tuple([len(v) for v in [fv, gv, tv, qv]]), (t_queries, q_query, f_query, g_query))

def verify_permutation(prf, s, h=None):
    if not h:
        h = Hash(F)
    om = _root_of_unity(s)
    cmts, ks, queries = prf
    kf, kg, kt, kq = ks
    t_queries, q_query, f_query, g_query = queries
    
    h.update(cmts[:2])
    r_ = h.digest()
    
    h.update(cmts[2:])
    r = h.digest()
    
    if not t_queries[0][0] == F(1):
        print("Product does not appear to be 1.")
        return False
    if not t_queries[2][0] * (r_ - g_query[0]) - t_queries[1][0] * (r_ - f_query[0]) == q_query[0] * (r^s - 1):
        print("Zero test on t1 failed.")
        return False
    
    f_cmt, g_cmt, t_cmt, q_cmt = cmts
    for i, query in zip([om^(s - 1), r, r * om], t_queries):
        if not poly_verify(t_cmt, kt, i, query[0], query[1], h):
            print("permutation test: poly verification failed on t")
            return False
    
    if not poly_verify(q_cmt, kq, r, q_query[0], q_query[1], h):
        print("permutation  test: poly verification failed on q")
        return False
    
    if not poly_verify(f_cmt, kf, om * r, f_query[0], f_query[1], h):
        print("permutation  test: poly verification failed on f")
        return False
    
    if not poly_verify(g_cmt, kg, om * r, g_query[0], g_query[1], h):
        print("permutation  test: poly verification failed on g")
        return False
    return True

def test_permutation(iterations):
    for _ in range(iterations):
        s = 4
        k = 8
        om = _root_of_unity(k)
        oms = [om^i for i in range(k)]
        
        # construct two polynomials f and g such that
        # f(omega^(i*k/s)) is a permutation of g(omega^(i*k/s))
        f_vals = [F.random_element() for _ in range(k)]
        g_vals = [F.random_element() for _ in range(k)]
        vals = [f_vals[i] for i in range(0, len(f_vals), k // s)]
        shuffle(vals)
        for i in range(len(vals)):
            g_vals[i * (k // s)] = vals[i]
        
        f = vector(F, pari.fftinv(oms, f_vals)) / F(k)
        g = vector(F, pari.fftinv(oms, g_vals)) / F(k)
        fpoly = P(list(f))
        gpoly = P(list(g))
        
        prf = prove_permutation(fpoly, gpoly, s)
        assert verify_permutation(prf, s), "Permutation test verification failed"

def _compute_lookup_permutations(f, t, selector=None):
    fl = sorted([sel * fi for sel, fi in zip(selector, f)])
    s = len(fl)
    
    tl = [0] * s
    tl[0] = fl[0]
    t.remove(fl[0])
    
    for i in range(1, s):
        if not fl[i] == fl[i - 1]:
            tl[i] = fl[i]
            t.remove(fl[i])
    
    for i in range(1, s):
        if fl[i] == fl[i - 1]:
            tl[i] = t.pop()
    
    return fl, tl
    
def _test_lookup_perms(iterations):
    for _ in range(iterations):
        t = list(range(4))
        f = [choice(t) for _ in range(10)]
        
        fl, tl = _compute_lookup_permutations(f, t + t[-1:] * (len(f) - len(t)))
        
        assert len(fl) == len(tl)
        assert fl[0] == tl[0]
        assert all(fl[i] == fl[i - 1] or fl[i] == tl[i] for i in range(1, len(fl)))

def _interpolate_pol(vals):
    s = len(vals)
    om = _root_of_unity(s)
    oms = [om^i for i in range(s)]
    return P(list(vector(F, pari.fftinv(oms, vals)) / F(s)))

# prove fpol(om^i) in list t for all i in range(s) and om an s-th root of unity 
def prove_lookup(fpol, t, selector, s, h=None):
    if not h:
        h = Hash(F)
    
    if selector == None:
        selector = [F(1)] * s
    
    f = P(fpol)
    t += t[-1:] * (s - len(t))
    tpol = _interpolate_pol(t)
    
    om = _root_of_unity(s)
    oms = [om^i for i in range(s)]
    fl = [f(omi) for omi in oms]
    
    fl, tl = _compute_lookup_permutations(fl, t, selector)
    
    selector_pol = _interpolate_pol(selector)
    f1 = _interpolate_pol(fl)
    t1 = _interpolate_pol(tl)
    
    pi1 = prove_permutation(selector_pol * f, f1, s, h)
    pi2 = prove_permutation(tpol, t1, s, h)
    
    Z = (f1(x) - t1(x)) * (f1(x) - f1(om^(-1) * x))
    
    ell_0 = (x^s - 1) / (s * (x - 1))
    
    alpha = h.digest()
    Z += alpha * ell_0 * (f1(x) - t1(x))
    
    q = P(Z / (x^s  - 1))
    
    qv = vector(q)
    
    q_cmt = poly_commit(qv)
    
    h.update([q_cmt[0]])
    r = h.digest()
    
    f1v = vector(f1)
    t1v = vector(t1)
    
    f1_prf = poly_open(f1v, r, h=h)
    f1_prf_ = poly_open(f1v, om^(-1) * r, h=h)
    t1_prf = poly_open(t1v, r, h=h)
    
    q_prf = poly_open(qv, r, cw=q_cmt[1], h=h)
    
    return (pi1, pi2), q_cmt[0], (f1_prf, f1_prf_, t1_prf, q_prf), (len(f1v), len(t1v), len(qv))

def verify_lookup(prf, s, h=None):
    if not h:
        h = Hash(F)
    
    perm_prfs, q_cmt, queries, degrees = prf
    pi1, pi2 = perm_prfs
    f1_prf, f1_prf_, t1_prf, q_prf = queries
    fk, tk, qk = degrees
    
    if not verify_permutation(pi1, s, h):
        print("lookup: permutation test on f failed")
        return False
    if not verify_permutation(pi2, s, h):
        print("lookup: permutation test on t failed")
        return False
    
    f1_cmt = pi1[0][1]
    t1_cmt = pi2[0][1]
    
    alpha = h.digest()
    
    h.update([q_cmt])
    r = h.digest()
    
    f1r, f1prf = f1_prf
    f1r_, f1prf_ = f1_prf_
    t1r, t1prf = t1_prf
    qr, qprf = q_prf
    
    zr = r^s - 1
    ell_0r = zr / (s * (r - 1))
    if not (f1r - t1r) * (f1r - f1r_ + alpha * ell_0r) == qr * zr:
        print("lookup zero test failed")
        return False
    
    if not poly_verify(f1_cmt, fk, r, f1r, f1prf, h):
        print("lookup: poly verification failed on f1.")
        return False
    om = _root_of_unity(s)
    if not poly_verify(f1_cmt, fk, om^(-1) * r, f1r_, f1prf_, h):
        print("lookup: poly verification failed on f1_.")
        return False
    
    if not poly_verify(t1_cmt, tk, r, t1r, t1prf, h):
        print("lookup: poly verification failed on t1.")
        return False
    
    if not poly_verify(q_cmt, qk, r, qr, qprf, h):
        print("lookup: poly verification failed on q.")
        return False
    
    return True
    
def test_lookup(iterations):
    for _ in range(iterations):
        s = 8
        t = list(range(-2, 2))
        selector = [randint(0,1) for _ in range(s)]
        f_vals = [choice(t) if sel else F.random_element() for sel in selector]
        
        om = _root_of_unity(s)
        oms = [om^i for i in range(s)]
        f = vector(F, pari.fftinv(oms, f_vals)) / F(s)
        
        prf = prove_lookup(P(list(f)), t, selector, s)
        assert verify_lookup(prf, s)

# prove that f(W(omega^i)) = g(omega^i) where W is a permutation on omega^i
def prove_prescribed_permutation(fpol, gpol, Wpol, s, h=None):
    if not h:
        h = Hash(F)
    
    f = P(fpol)
    g = P(gpol)
    W = P(Wpol)
    fv = vector(f)
    gv = vector(g)
    Wv = vector(W)
    
    cmts = [poly_commit(v) for v in [fv, gv, Wv]]
    h.update(cmts)
    r_ = h.digest()
    h.update([F(0)])
    s_ = h.digest()
    
    om = _root_of_unity(s)
    oms = [om^i for i in range(s)]
    fhat = r_ - s_ * W - f
    ghat = r_ - s_ * x - g
    t_vals = functools.reduce(lambda x, y: x + [x[-1] * fhat(y) / ghat(y)], oms[1:], [fhat(oms[0]) / ghat(oms[0])])
    
    t = P(list( vector(F, pari.fftinv(oms, t_vals)) / F(s) ))
    t1 = t(om * x) * ghat(om * x) - t(x) * fhat(om * x)
    q = P(t1 / (x^s - 1))
    
    
    tv = vector(t)
    qv = vector(q)
    
    cmts_ = [poly_commit(tv), poly_commit(qv)]
    
    h.update(cmts_)
    r = h.digest()
    
    cmts += cmts_
    
    t_queries = [poly_open(tv, point, h) for point in [oms[-1], r, r * om]]
    q_query = poly_open(qv, r, h)
    f_query = poly_open(fv, om * r, h)
    g_query = poly_open(gv, om * r, h)
    W_query = poly_open(Wv, om * r, h)
    return (cmts, tuple([len(v) for v in [fv, gv, Wv, tv, qv]]), (t_queries, q_query, f_query, g_query, W_query))

def verify_prescribed_permutation(prf, s, h=None):
    if not h:
        h = Hash(F)
    om = _root_of_unity(s)
    cmts, ks, queries = prf
    f_cmt, g_cmt, W_cmt, t_cmt, q_cmt = cmts
    kf, kg, kW, kt, kq = ks
    t_queries, q_query, f_query, g_query, W_query = queries
    
    h.update(cmts[:3])
    r_ = h.digest()
    h.update([F(0)])
    s_ = h.digest()
    
    h.update(cmts[3:])
    r = h.digest()
    
    if not t_queries[0][0] == F(1):
        print("Product does not appear to be 1.")
        return False
    
    lhs1 = t_queries[2][0] * (r_ - s_ * om * r - g_query[0])
    lhs2 = t_queries[1][0] * (r_ - s_ * W_query[0] - f_query[0])
    lhs = lhs1 - lhs2
    rhs = q_query[0] * (r^s - 1)
    if not lhs == rhs:
        print(f"Zero test on t1 failed: lhs = {lhs} != {rhs} = rhs")
        return False
    
    for i, query in zip([om^(s - 1), r, r * om], t_queries):
        if not poly_verify(t_cmt, kt, i, query[0], query[1], h):
            print("permutation test: poly verification failed on t")
            return False
    
    if not poly_verify(q_cmt, kq, r, q_query[0], q_query[1], h):
        print("permutation  test: poly verification failed on q")
        return False
    
    if not poly_verify(f_cmt, kf, om * r, f_query[0], f_query[1], h):
        print("permutation  test: poly verification failed on f")
        return False
    
    if not poly_verify(g_cmt, kg, om * r, g_query[0], g_query[1], h):
        print("permutation  test: poly verification failed on g")
        return False
    
    if not poly_verify(W_cmt, kW, om * r, W_query[0], W_query[1], h):
        print("permutation  test: poly verification failed on W")
        return False
    
    return True

def test_prescribed_permutation(iterations):
    for _ in range(iterations):
        s = 4
        k = 8
        om = _root_of_unity(k)
        oms = [om^i for i in range(k)]
        
        # construct two polynomials f and g such that
        # f(omega^(i*k/s)) is a permutation of g(omega^(i*k/s))
        f_vals = [F.random_element() for _ in range(k)]
        g_vals = [F.random_element() for _ in range(k)]
        vals = [f_vals[i] for i in range(0, len(f_vals), k // s)]
        pi = [i - 1 for i in Permutations(s).random_element()]
        for i in range(s):
            g_vals[pi[i] * (k // s)] = vals[i]
        
        om_s = _root_of_unity(s)
        W_vals = [om_s^(pi[i]) for i in range(s)]
        
        f = vector(F, pari.fftinv(oms, f_vals)) / F(k)
        g = vector(F, pari.fftinv(oms, g_vals)) / F(k)
        W = vector(F, pari.fftinv([om_s^i for i in range(s)], W_vals)) / F(s)
        
        
        fpoly = P(list(f))
        gpoly = P(list(g))
        Wpoly = P(list(W))
        
        prf = prove_prescribed_permutation(fpoly, gpoly, Wpoly, s)
        if not verify_prescribed_permutation(prf, s):
            print(f)
            print(g)
            print(pi)
            print(W)
            return False
        assert verify_prescribed_permutation(prf, s), "Prescribed permutation test verification failed"

def test_all_gadgets(iterations):
    test_poly_product(iterations)
    test_zero(iterations)
    test_prod(iterations)
    test_prod_rational(iterations)
    test_permutation(iterations)
    test_prescribed_permutation(iterations)
