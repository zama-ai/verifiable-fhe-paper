# PLONK + FRI based SNARK
import functools
from collections import OrderedDict

load("poly_fri.sage")

class TwiddleFactory:
    def __init__(self, omega, d_max):
        self.omegas = [1]
        for _ in range(d_max - 1):
            self.omegas.append(self.omegas[-1] * omega)
        self.d_max = d_max
    
    def twiddles(self, d):
        step = self.d_max // d
        return self.omegas[::step]

class PlonkPoly:
    P = None
    TF = None
    
    def __init__(self, d_max):
        self.poly = None
        self.vector = None
        self.ntt = None
        self.d_max = d_max
        self.points_to_open = []
    
    def from_poly(poly, d_max=None):
        if d_max == None:
            d_max = PlonkPoly.P(poly).degree() + 1
        ppoly = PlonkPoly(d_max)
        ppoly.poly = PlonkPoly.P(poly)
        return ppoly
    
    def from_vals(vals, d_max=None):
        if d_max == None:
            d_max = len(vals)
        ppoly = PlonkPoly(d_max)
        if len(vals) == d_max:
            ppoly.ntt = vector(PlonkPoly.P.base_ring(), vals)
        else:
            ppoly.poly = PlonkPoly._interpolate(vals)
        return ppoly
    
    def as_poly(self):
        if self.poly == None:
            if self.ntt == None:
                raise ValueError("Plonk poly unspecified.")
            self.poly = PlonkPoly._interpolate(self.ntt)
        return self.poly
    
    def as_vector(self):
        if self.vector == None:
            if self.poly == None:
                self.as_poly()
            F = PlonkPoly.P.base_ring()
            self.vector = vector(F, self.poly) if self.poly else zero_vector(F, 1)
        return self.vector
    
    def as_vals(self, d):
        F = PlonkPoly.P.base_ring()
        if self.ntt == None:
            if self.poly == None:
                raise ValueError("Plonk poly unspecified.")
            # ~ print("NTT not known yet. Need to compute.")
            twiddles = PlonkPoly.TF.twiddles(self.d_max)
            self.ntt = vector(F, pari.fft(twiddles, self.poly))
        step = self.d_max // d
        return self.ntt[::step]
    
    def _interpolate(vals):
        d = len(vals)
        twiddles = PlonkPoly.TF.twiddles(d)
        F = PlonkPoly.P.base_ring()
        if not ZZ(d).is_power_of(2):
            raise NotImplementedError("Interpolation of non-power-of-two vectors not supported.")
        return PlonkPoly.P(pari.fftinv(twiddles, vals)) / F(d)
    
    def __add__(self, other):
        if isinstance(other, PlonkPoly):
            return PlonkPoly.from_poly(self.as_poly() + other.as_poly())
        else:
            # assuming other is a plain poly
            return PlonkPoly.from_poly(self.as_poly() + other)
    
    def __sub__(self, other):
        return PlonkPoly.from_poly(self.as_poly() - other.as_poly())
    
    # naive multiplication. use as_vals() for ntt based multiplication
    def __mul__(self, other):
        if isinstance(other, PlonkPoly):
            return PlonkPoly.from_poly(self.as_poly() * other.as_poly())
        else:
            # assuming scalar multiplication
            return PlonkPoly.from_poly(other * self.as_poly())
    
    # will throw an error if not divisible
    def __truediv__(self, other):
        return PlonkPoly.from_poly(self.as_poly() / other.as_poly())
    
    def test():
        d_max = 32
        d = 8
        poly_fri = PolyFRI(p, beta, ell)
        P = poly_fri.get_poly_ring()
        PlonkPoly.P = P
        PlonkPoly.TF = TwiddleFactory(poly_fri.root_of_unity(d_max), d_max)
        
        F = P.base_ring()
        poly1 = P([F.random_element() for _ in range(d)])
        ppoly1 = PlonkPoly.from_poly(poly1, d_max)
        
        poly2 = [F.random_element() for _ in range(d)]
        ppoly2 = PlonkPoly.from_vals(poly2, d_max)
        
        ntt1 = ppoly1.as_vals(2 * d)
        ntt2 = ppoly2.as_vals(2 * d)
        
        result = PlonkPoly.from_vals(ntt1.pairwise_product(ntt2))
        assert result.as_poly() == ppoly1.as_poly() * ppoly2.as_poly()

class Plonk:
    def __init__(self, pcs):
        self.columns = 3
        self.pcs = pcs
        self.P = pcs.get_poly_ring()
    
    def _circuit_sizes(C, I, W):
        d = FRI._next_pow_of_2(C + I + W)
        return C, I + W, d

    def _to_eval_polys(self, trace, inputs, witness):
        d = self.d
        
        print(d, len(trace), len(inputs), len(witness))
        
        l_vals = []
        r_vals = []
        o_vals = []
        for gate in trace:
            l_vals.append(gate[0])
            r_vals.append(gate[1])
            o_vals.append(gate[2])
        for noop in range(d - len(trace) - len(inputs) - len(witness)):
            l_vals.append(0)
            r_vals.append(0)
            o_vals.append(0)
        for x in (inputs + witness)[::-1]:
            l_vals.append(x)
            r_vals.append(0)
            o_vals.append(0)
        
        print(f"Interpolating poly in dim {self.d_max}")
        t = cputime()
        Lpoly = PlonkPoly.from_vals(l_vals, self.d_max)
        # ~ Rpoly = PlonkPoly.from_vals(r_vals, d)
        # ~ Opoly = PlonkPoly.from_vals(o_vals, d)
        Rpoly = PlonkPoly.from_vals(r_vals, self.d_max)
        Opoly = PlonkPoly.from_vals(o_vals, self.d_max)
        
        print(f"Done in {cputime(t)}s")
        return Lpoly, Rpoly, Opoly
    
    def _input_poly(self, inputs):
        # ~ return self.P.lagrange_polynomial([(w, inp) for w, inp in zip(self.input_omegas, inputs)])
        return self.P(pari.polinterpolate(self.input_omegas, inputs))
        

    def _prove_inputs(self, ivp, T, inputs, h):
        v = PlonkPoly.from_poly(self._input_poly(inputs))
        q = (T - v) / ivp
        
        # already committed to T
        q_cmt = self.pcs.commit(q.as_vector())
        
        h.update_raw([q_cmt])
        r = h.digest()
        
        T.points_to_open.append(r)
        q_prf = self.pcs.open(q.as_vector(), r, h)
        ivp_prf = self.pcs.open(ivp.as_vector(), r, h)
        
        return q_cmt, q_prf, ivp_prf, len(q.as_vector())
    
    def _verify_inputs(self, ivp_cmt, T_cmt, inputs, prf_inp, t_points, h):
        print("\tTesting points.")
        t = cputime()
        q_cmt, q_prf, ivp_prf, kq = prf_inp
        v = self._input_poly(inputs)
        print(f"\t\tInput poly computed {cputime(t)}.")
        
        h.update_raw([q_cmt])
        r = h.digest()
        
        if not r in t_points:
            print("input test: point not opened.")
            return False
        
        t_r = t_points[r]
        if not t_r - v(r) == q_prf[0] * ivp_prf[0]:
            print("zero test failed.")
            return False
        
        print(f"\tDone in {cputime(t)}s. Verifying openings." )
        if not self.pcs.verify(q_cmt, kq, r, q_prf[0], q_prf[1], h):
            print("input test: poly verification on q failed.")
            return False
        
        if not self.pcs.verify(ivp_cmt, len(inputs) + 1, r, ivp_prf[0], ivp_prf[1], h):
            print("input test: poly verification on IVP failed.")
            return False
        
        print(f"\tDone in {cputime(t)}s (cum)." )
        return True

    def _prove_gates(self, selectors, T, h):
        L, R, O = T
        S_add, S_mul, S_con = selectors
        
        print("\tcomputing q.")
        t = cputime()
        x = self.P.gen()
        g = S_add * (L + R) + S_mul * L * R + S_con - O
        # O(x) needs to be 0 for all x in {omega^i: i in range(C, d)}
        # doesn't matter for L and R because selectors will be 0
        q = g / PlonkPoly.from_poly(x^self.d - 1)
        print(f"\tDone in {cputime(t)}s")
        
        print(f"\tcomputing commit to degree-{q.as_poly().degree()} poly q.")
        t = cputime()
        q_cmt = self.pcs.commit(q.as_vector())
        print(f"\tDone in {cputime(t)}s")
        
        h.update_raw([q_cmt])
        r = h.digest()
        
        print("\ttime to open.")
        t = cputime()
        s_add_query = self.pcs.open(S_add.as_vector(), r, h)
        s_mul_query = self.pcs.open(S_mul.as_vector(), r, h)
        s_con_query = self.pcs.open(S_con.as_vector(), r, h)
        q_query = self.pcs.open(q.as_vector(), r, h)
        
        L.points_to_open.append(r)
        R.points_to_open.append(r)
        O.points_to_open.append(r)
        
        print(f"\tDone in {cputime(t)}s")
        
        queries = (s_add_query, s_mul_query, s_con_query, q_query)
        return q_cmt, len(q.as_vector()), queries
    
    def _verify_gates(self, selector_cmts, T_cmts, prf_gates, l_points, r_points, o_points, h):
        print("\tTesting points.")
        t = cputime()
        Lcmt, Rcmt, Ocmt = T_cmts
        q_cmt, kq, queries = prf_gates
        s_add_query, s_mul_query, s_con_query, q_query = queries
        
        h.update_raw([q_cmt])
        r = h.digest()
        
        sar, _ = s_add_query
        smr, _ = s_mul_query
        scr, _ = s_con_query
        
        for points in [l_points, r_points, o_points]:
            if r not in points:
                print("gates test: point not opened")
                return False
        
        l_r = l_points[r]
        r_r = r_points[r]
        o_r = o_points[r]
        
        qr, _ = q_query
        
        d = self.d
        zr = r^d - 1
        if not qr * zr == sar * (l_r + r_r) + smr * l_r * r_r + scr - o_r:
            print("zero test on gates failed.")
            return False
        
        cmts = list(selector_cmts) + [q_cmt]
        ks = [d] * 3 + [kq]
        print(f"\tDone in {cputime(t)}s. Verifying openings." )
        for cmt, k, query in zip(cmts, ks, queries):
            if not self.pcs.verify(cmt, k, r, query[0], query[1], h):
                print("gates test: some poly verification failed.")
                return False
        
        print(f"\tDone in {cputime(t)}s (cum)." )
        
        return True

    def _prove_wires(self, wire_polys, T, h):
        L, R, O = T
        d = self.d
        d_max = self.d_max
        
        SID, S_l, S_r, S_o, perm = wire_polys
        
        # prove permutation
        beta = h.digest()
        F = self.P.base_ring()
        h.update([F(0)])
        gamma = h.digest()
        
        print(f"\tcomputing f and g")
        t = cputime()
        
        # ~ f_l = L + SID * beta + gamma
        # ~ f_r = R + (SID + d) * beta + gamma
        # ~ f_o = O + (SID + 2 * d) * beta + gamma
        
        # ~ g_l = L + S_l * beta + gamma
        # ~ g_r = R + S_r * beta + gamma
        # ~ g_o = O + S_o * beta + gamma
        
        # ~ f = f_l * f_r * f_o
        # ~ g = g_l * g_r * g_o
        
        # ~ f.d_max = self.d_max
        # ~ g.d_max = self.d_max
        
        gamma_ = vector(F, [gamma for _ in range(d_max)])
        d_ = vector(F, [d for _ in range(d_max)])
        
        f_l = L.as_vals(d_max) + beta * SID.as_vals(d_max) + gamma_
        f_r = R.as_vals(d_max) + beta * (SID.as_vals(d_max) + d_) + gamma_
        f_o = O.as_vals(d_max) + beta * (SID.as_vals(d_max) + 2 * d_) + gamma_
        
        g_l = L.as_vals(d_max) + beta * S_l.as_vals(d_max) + gamma_
        g_r = R.as_vals(d_max) + beta * S_r.as_vals(d_max) + gamma_
        g_o = O.as_vals(d_max) + beta * S_o.as_vals(d_max) + gamma_
        
        fv = f_l.pairwise_product(f_r).pairwise_product(f_o)
        gv = g_l.pairwise_product(g_r).pairwise_product(g_o)
        
        f = PlonkPoly.from_vals(fv)
        g = PlonkPoly.from_vals(gv)
        
        print(f"\tf and g polys computed after {cputime(t)}s")
        
        t = cputime()
        f_vals = f.as_vals(d)
        g_vals = g.as_vals(d)
        # vals = functools.reduce(lambda x, y: x + [x[-1] * y[0]/y[1]], zip(f_vals[1:], g_vals[1:]), [f_vals[0] / g_vals[0]])
        # -- This one seems slower than second version, but both are likewise
        # vals = [f_vals[0]/g_vals[0]]
        # for i in range(1,len(vals)):
        #    vals.append(vals[-1] * f_vals[i]/g_vals[i]);
        # //-- END slower one
        vals = [ _f/_g for _f,_g in zip(f_vals, g_vals) ];
        for i in range(1, len(vals)):
            vals[i] *= vals[i-1];
        print(f"\tComputing vals using trace: {cputime(t)}s")
        
        print("\tComputing Z poly.")
        t = cputime()
        Z = PlonkPoly.from_vals(vals, self.d_max)
        print(f"\tDone in {cputime(t)}s")
        
        print("\tComputing Z1 poly.")
        t = cputime()
        
        Zhat = list(Z.as_vals(self.d_max))
        ghat = list(g.as_vals(self.d_max))
        fhat = list(f.as_vals(self.d_max))
        
        left = vector(F, Zhat[4:] + Zhat[:4]).pairwise_product(vector(F, ghat[4:] + ghat[:4]))
        right = vector(F, Zhat).pairwise_product(vector(F, fhat[4:] + fhat[:4]))
        Z1 = PlonkPoly.from_vals(left - right)
        print(f"\tDone in {cputime(t)}s. Z1 degree is {Z1.as_poly().degree()} where d is {d}.")
        # ~ print("Dividing by vanishing poly.")
        # ~ t = cputime()
        # ~ q = P(Z1 / (x^d - 1))
        # ~ qv = vector(q)
        # ~ print(f"Done in {cputime(t)}s")
        print("\tDividing by vanishing poly.")
        t = cputime()
        qc = list(Z1.as_poly()); # Could also never transform back and forth between list and polys
        dZ1 = len(qc); # dZ1 = deg qc + 1
        for _k in range(dZ1-1, 2*d-1, -1):
            qc[_k-d] += qc[_k]
        q = PlonkPoly.from_poly(qc[d:])
        print(f"\tDone in {cputime(t)}s")
        
        Zcmt = self.pcs.commit(Z.as_vector())
        q_cmt = self.pcs.commit(q.as_vector())
        cmts = [Zcmt, q_cmt]
        
        h.update_raw(cmts)
        
        r = h.digest()
        
        print("\ttime to open.")
        t = cputime()
        omega = self.tf.twiddles(d)[1]
        Z_queries = self.pcs.open(Z.as_vector(), [self.tf.twiddles(d)[-1], r, omega * r], h)
        q_query = self.pcs.open(q.as_vector(), r, h)
        L.points_to_open.append(omega * r)
        R.points_to_open.append(omega * r)
        O.points_to_open.append(omega * r)
        
        SID_query = self.pcs.open(SID.as_vector(), omega * r, h)
        Sl_query = self.pcs.open(S_l.as_vector(), omega * r, h)
        Sr_query = self.pcs.open(S_r.as_vector(), omega * r, h)
        So_query = self.pcs.open(S_o.as_vector(), omega * r, h)
        print(f"\tDone in {cputime(t)}s")
        return cmts, len(q.as_vector()), (Z_queries, q_query, SID_query, Sl_query, Sr_query, So_query)

    
    def _verify_wires(self, wire_cmts, Tcmts, prf_wires, l_points, r_points, o_points, h):
        print("\tTesting points.")
        t = cputime()
        d = self.d
        cmts, kq, queries = prf_wires
        Z_queries, q_query, SID_query, Sl_query, Sr_query, So_query = queries
        Zcmt, q_cmt = cmts
        
        beta = h.digest()
        F = self.P.base_ring()
        h.update([F(0)])
        gamma = h.digest()
        
        h.update_raw([Zcmt, q_cmt])
        r = h.digest()
        
        Z_points, Z_prf = Z_queries
        if not Z_points[0] == F(1):
            print("wiring test: Product does not appear to be 1.")
            return False
        
        omega = self.tf.twiddles(d)[1]
        omegar = omega * r
        
        for points in [l_points, r_points, o_points]:
            if omegar not in points:
                print("wiring test: point not opened")
                return False
        
        l_r = l_points[omegar]
        r_r = r_points[omegar]
        o_r = o_points[omegar]
        
        # ~ f_l = L_query[0] + beta * SID_query[0] + gamma
        # ~ f_r = R_query[0] + beta * (SID_query[0] + d) + gamma
        # ~ f_o = O_query[0] + beta * (SID_query[0] + 2 * d) + gamma
        
        # ~ g_l = L_query[0] + beta * Sl_query[0] + gamma
        # ~ g_r = R_query[0] + beta * Sr_query[0] + gamma
        # ~ g_o = O_query[0] + beta * So_query[0] + gamma
        f_l = l_r + beta * SID_query[0] + gamma
        f_r = r_r + beta * (SID_query[0] + d) + gamma
        f_o = o_r + beta * (SID_query[0] + 2 * d) + gamma
        
        g_l = l_r + beta * Sl_query[0] + gamma
        g_r = r_r + beta * Sr_query[0] + gamma
        g_o = o_r + beta * So_query[0] + gamma
        
        f = f_l * f_r * f_o
        g = g_l * g_r * g_o
        
        
        lhs1 = Z_points[2] * g
        lhs2 = Z_points[1] * f
        lhs = lhs1 - lhs2
        rhs = q_query[0] * (r^d - 1)
        if not lhs == rhs:
            print(f"Zero test on t1 failed: lhs = {lhs} != {rhs} = rhs")
            return False
        
        print(f"\tDone in {cputime(t)}s. Verifying openings." )
        
        if not self.pcs.verify(Zcmt, d, [omega^(d - 1), r, r * omega], Z_points, Z_prf, h):
            print("permutation test: poly verification failed on Z")
            return False
        
        if not self.pcs.verify(q_cmt, kq, r, q_query[0], q_query[1], h):
            print("permutation  test: poly verification failed on q")
            return False
        
        for cmt, query in zip(list(wire_cmts), queries[2:]):
            if not self.pcs.verify(cmt, d, omega * r, query[0], query[1], h):
                print("permutation  test: poly verification failed on some poly")
                return False
        print(f"\tDone in {cputime(t)}s (cum)." )
        return True
    
    def _lookup_permutations(self, f, selector):
        t = copy(self.lu_table)
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

    def _list_left_rot_to_vec(self, lst, rot):
        F = self.P.base_ring()
        return vector(F, lst[rot:] + lst[:rot])

    def _prove_lookups(self, lu_polys, T, h):
        d = self.d
        t_poly, S = lu_polys
        F = self.P.base_ring()
        
        # permute values in S*T and table
        Tvals_sorted, t_sorted = self._lookup_permutations(T.as_vals(d), S.as_vals(d))
        
        T_sorted = PlonkPoly.from_vals(Tvals_sorted, self.d_max)
        t_poly_sorted = PlonkPoly.from_vals(t_sorted, self.d_max)
        
        Ts_cmt = self.pcs.commit(T_sorted.as_vector())
        ts_cmt = self.pcs.commit(t_poly_sorted.as_vector())
        
        cmts = [Ts_cmt, ts_cmt]
        h.update_raw(cmts)
        
        # permutation challenges
        beta = h.digest()
        h.update([F(0)])
        gamma = h.digest()
        
        # batched permutation argument
        t = cputime()
        f_vals = [(s_val * t_val + beta) * (F(t_poly_val) + gamma) for s_val, t_val, t_poly_val in zip(S.as_vals(d), T.as_vals(d), self.lu_table)]
        g_vals = [(Ts_val + beta) * (ts_val + gamma) for Ts_val, ts_val in zip(Tvals_sorted, t_sorted)]
        Z_vals = [ _f/_g for _f,_g in zip(f_vals, g_vals) ]
        for i in range(1, d):
            Z_vals[i] *= Z_vals[i-1];
        print(f"\tComputing vals using trace: {cputime(t)}s")
        
        Z = PlonkPoly.from_vals(Z_vals, self.d_max)
        Z_cmt = self.pcs.commit(Z.as_vector())
        
        h.update_raw([Z_cmt])
        cmts.append(Z_cmt)
        
        alpha = h.digest()
        h.update([F(0)])
        delta = h.digest()
        h.update([F(0)])
        eta = h.digest()
        
        print("\tComputing Z1 poly in steps.")
        t = cputime()
        
        Zhat = list(Z.as_vals(self.d_max))
        That = list(T.as_vals(self.d_max))
        Tshat = list(T_sorted.as_vals(self.d_max))
        that = list(t_poly.as_vals(self.d_max))
        tshat = list(t_poly_sorted.as_vals(self.d_max))
        Shat = list(S.as_vals(self.d_max))
        
        beta_v = vector(F, [beta for _ in range(4*d)])
        gamma_v = vector(F, [gamma for _ in range(4*d)])
        print(f"\t\tStep 0: {cputime(t)}s.")
        
        Z1hat_1 = self._list_left_rot_to_vec(Zhat, 4).pairwise_product(self._list_left_rot_to_vec(Tshat, 4) + beta_v)
        Z1hat_1 = Z1hat_1.pairwise_product(self._list_left_rot_to_vec(tshat, 4) + gamma_v)
        print(f"\t\tStep 1: {cputime(t)}s.")
        
        Z1hat_2 = vector(F, Zhat).pairwise_product(self._list_left_rot_to_vec(Shat, 4).pairwise_product(self._list_left_rot_to_vec(That, 4)) + beta_v) 
        Z1hat_2 = Z1hat_2.pairwise_product(self._list_left_rot_to_vec(that, 4) + gamma_v)
        print(f"\t\tStep 2: {cputime(t)}s.")
        
        Z1hat_3 = (vector(F, Tshat) - vector(F, tshat)).pairwise_product(vector(F, Tshat) - self._list_left_rot_to_vec(Tshat, 4 * (d - 1)))
        Z1hat_3 *= delta
        print(f"\t\tStep 3: {cputime(t)}s.")
        
        Z1 = PlonkPoly.from_vals(Z1hat_1 - Z1hat_2 + Z1hat_3)
        print(f"\t\tStep 4: {cputime(t)}s.")
        
        x = self.P.gen()
        twiddles = self.tf.twiddles(d)
        omega = twiddles[1]
        ell = PlonkPoly.from_poly(alpha * (x^d - 1) / (omega * d * (x - twiddles[-1])))
        Z1 = Z1 + ell * (Z * (-1) + 1)
        ell_0 = PlonkPoly.from_poly(eta * (x^d - 1) / (d * (x - 1)))
        Z1 +=  ell_0 * (T_sorted - t_poly_sorted)
        print(f"\t\tStep 5: {cputime(t)}s.")
        
        # prove Z1 vanishes on all omega^i
        # q = P(Z1 / (x^d - 1))
        # qv = vector(F, q)
        qc = list(Z1.as_poly()); # Could also never transform back and forth between list and polys
        dZ1 = len(qc); # dZ1 = deg qc + 1
        for _k in range(dZ1-1, 2*d-1, -1):
            qc[_k-d] += qc[_k]
        q = PlonkPoly.from_poly(qc[d:])
        
        q_cmt = self.pcs.commit(q.as_vector())
        
        cmts.append(q_cmt)
        h.update_raw([q_cmt])
        r = h.digest()
        
        print("\ttime to open.")
        t = cputime()
        Z_queries = self.pcs.open(Z.as_vector(), [r, omega*r], h=h)
        S_query = self.pcs.open(S.as_vector(), omega * r, h=h)
        
        T.points_to_open.append(omega * r)
        
        t_query = self.pcs.open(t_poly.as_vector(), omega * r, h=h)
        Ts_queries = self.pcs.open(T_sorted.as_vector(), [r / omega, r, omega * r], h=h)
        ts_queries = self.pcs.open(t_poly_sorted.as_vector(), [r, omega * r], h=h)
        q_query = self.pcs.open(q.as_vector(), r, h=h)
        print(f"\tDone in {cputime(t)}s")
        
        queries = Z_queries, S_query, t_query, Ts_queries, ts_queries, q_query
        
        return cmts, queries, tuple([len(v.as_vector()) for v in [Z, S, T, t_poly, T_sorted, t_poly_sorted, q]])

    def _verify_lookups(self, lu_cmts, cmt, prf_lu, t_points, h):
        print("\tTesting points.")
        t = cputime()
        t_cmt, S_cmt = lu_cmts
        cmts, queries, ks = prf_lu
        Ts_cmt, ts_cmt, Z_cmt, q_cmt = cmts
        Z_queries, S_query, t_query, Ts_queries, ts_queries, q_query = queries
        Zk, Sk, Tk, tk, Tsk, tsk, qk = ks
        
        h.update_raw([Ts_cmt, ts_cmt])
        beta = h.digest()
        F = self.P.base_ring()
        h.update([F(0)])
        gamma = h.digest()
        
        h.update_raw([Z_cmt])
        alpha = h.digest()
        h.update([F(0)])
        delta = h.digest()
        h.update([F(0)])
        eta = h.digest()
        
        h.update_raw([q_cmt])
        r = h.digest()
        
        d = self.d
        omega = self.tf.twiddles(d)[1]
        if omega * r not in t_points:
            print("lookup test: point not opened.")
            return False
        T_r = t_points[omega * r]
        
        Z_points, Z_prf = Z_queries
        Ts_points, Ts_prf = Ts_queries
        ts_points, ts_prf = ts_queries
        
        lhs = Z_points[-1] * (Ts_points[-1] + beta) * (ts_points[-1] + gamma)
        lhs -= Z_points[0] * (S_query[0] * T_r + beta) * (t_query[0] + gamma)
        
        zr = (r^d - 1)
        ell_r = zr / (omega * d * (r - 1 / omega))
        ell_0_r = zr / (d * (r - 1))
        lhs += alpha * ell_r * (1 - Z_points[0])
        
        lhs += delta * (Ts_points[1] - ts_points[0]) * (Ts_points[1] - Ts_points[0])
        lhs += eta * ell_0_r * (Ts_points[1] - ts_points[0])
        
        rhs = q_query[0] * zr
        
        if lhs != rhs:
            print("lookup verification failed.")
            return False
        
        print(f"\tDone in {cputime(t)}s. Verifying openings." )
        
        if not self.pcs.verify(Z_cmt, Zk, [r, omega*r], Z_points, Z_prf, h):
            print("lookup test: poly verification failed on Z")
            return False
        
        if not self.pcs.verify(S_cmt, Sk, omega * r, S_query[0], S_query[1], h):
            print("lookup test: poly verification failed on S")
            return False
        
        if not self.pcs.verify(t_cmt, tk, omega * r, t_query[0], t_query[1], h):
            print("lookup test: poly verification failed on t")
            return False
        
        if not self.pcs.verify(Ts_cmt, Tsk, [r / omega, r, omega * r], Ts_points, Ts_prf, h):
            print("lookup test: poly verification failed on Ts")
            return False
        
        if not self.pcs.verify(ts_cmt, tsk, [r, omega * r], ts_points, ts_prf, h):
            print("lookup test: poly verification failed on ts")
            return False
        
        if not self.pcs.verify(q_cmt, qk, r, q_query[0], q_query[1], h):
            print("lookup test: poly verification failed on q")
            return False
        print(f"\tDone in {cputime(t)}s (cum)." )
        return True
    
    def _perm_term_to_in_out(term):
        return {term[i] : term[(i+1) % len(term)] for i in range(len(term))}
    
    def _re_index_wire(self, i, d):
        if i < 0:
            return d + i
        c = i % self.columns
        r = i // self.columns
        return c * d + r

    def _format_wires(self, wires, d):
        w_dic = {}
        for term in wires:
            w_dic.update(Plonk._perm_term_to_in_out([self._re_index_wire(i, d) for i in term]))
        
        for i in range(self.columns * d):
            if not i in w_dic:
                w_dic[i] = i
        
        return w_dic
    
    def preprocess_circuit(self, C, I, W, selectors, wires, lookup_data=None):
        print("Preprocessing circuit")
        t_top = cputime()
        d = FRI._next_pow_of_2(C + I + W)
        self.d = d
        self.d_max = 4 * self.d
        
        omega = self.pcs.root_of_unity(self.d_max)
        tf = TwiddleFactory(omega, self.d_max)
        self.tf = tf
        PlonkPoly.P = self.P
        PlonkPoly.TF = tf
        
        # inputs
        self.input_omegas = tf.twiddles(d)[:-(I + 1):-1]
        x = self.P.gen()
        input_vanish_poly = PlonkPoly.from_poly(prod([x - omi for omi in self.input_omegas]))
        ivp_cmt = self.pcs.commit(input_vanish_poly.as_vector())
        
        # gates
        selector_add, selector_mul, selector_con = selectors
        # compute selector polynomials
        S_add = PlonkPoly.from_vals([selector_add[i] if i in selector_add else 0 for i in range(d)], self.d_max)
        S_mul = PlonkPoly.from_vals([selector_mul[i] if i in selector_mul else 0 for i in range(d)], self.d_max)
        S_con = PlonkPoly.from_vals([selector_con[i] if i in selector_con else 0 for i in range(d)], self.d_max)
        
        print("\tcomputing commits to S polys.")
        t = cputime()
        S_add_cmt = self.pcs.commit(S_add.as_vector())
        S_mul_cmt = self.pcs.commit(S_mul.as_vector())
        S_con_cmt = self.pcs.commit(S_con.as_vector())
        print(f"\tDone in {cputime(t)}s")
        selector_polys = S_add, S_mul, S_con
        selector_cmts = S_add_cmt, S_mul_cmt, S_con_cmt
        
        # wires
        SID = PlonkPoly.from_vals(list(range(d)), self.d_max)
        # construct wiring polynomials
        perm = self._format_wires(wires, d)
        S_l = PlonkPoly.from_vals([perm[i] for i in range(d)], self.d_max)
        S_r = PlonkPoly.from_vals([perm[i] for i in range(d, 2 * d)], self.d_max)
        S_o = PlonkPoly.from_vals([perm[i] for i in range(2 * d, 3 * d)], self.d_max)
        
        SID_cmt = self.pcs.commit(SID.as_vector())
        Sl_cmt = self.pcs.commit(S_l.as_vector())
        Sr_cmt = self.pcs.commit(S_r.as_vector())
        So_cmt = self.pcs.commit(S_o.as_vector())
        
        wire_polys = SID, S_l, S_r, S_o, perm
        wire_cmts = SID_cmt, Sl_cmt, Sr_cmt, So_cmt
        
        # force precomputation of NTT of selectors
        S_add.as_vals(d)
        S_mul.as_vals(d)
        S_con.as_vals(d)
        SID.as_vals(d)
        S_l.as_vals(d)
        S_r.as_vals(d)
        S_o.as_vals(d)
        
        # lookups
        lu_polys = None
        lu_cmts = None
        if lookup_data != None:
            selector, table = lookup_data
            
            # pad the selector values and line up with T poly
            vals = {}
            min_id = min(selector.keys())
            for i in range(min_id, d):
                if (i % d) not in vals:
                    vals[i % d] = selector[i] if i in selector else 0
            
            # pad the table
            if len(table) > d:
                raise NotImplementedError("tables larger than the witness length not supported yet.")
            table += table[-1:] * (d - len(table))
            t_poly = PlonkPoly.from_vals(table, self.d_max)
            self.lu_table = table
            
            F = self.P.base_ring()
            
            print("\tcomputing commit to table poly.")
            t = cputime()
            t_cmt = self.pcs.commit(t_poly.as_vector())
            print(f"\tDone in {cputime(t)}s")
            
            # compute selector polynomial
            S = PlonkPoly.from_vals([vals[i] for i in range(d)], self.d_max)
            print("\tcomputing commit to S poly.")
            t = cputime()
            S_cmt = self.pcs.commit(S.as_vector())
            print(f"\tDone in {cputime(t)}s")
            lu_polys = t_poly, S
            lu_cmts = t_cmt, S_cmt
            
            t_poly.as_vals(d)
            S.as_vals(d)
        
        prover_input = input_vanish_poly, selector_polys, wire_polys, lu_polys
        verifier_input = ivp_cmt, selector_cmts, wire_cmts, lu_cmts
        
        print(f"Done in {cputime(t_top)}s")
        return prover_input, verifier_input
    
    def prove(self, prover_input, trace, inputs, witness, h=None):
        print("Proving circuit.")
        t_top = cputime()
        
        F = self.P.base_ring()
        
        if not h:
            h = Hash(F)
        
        ivp, selector_polys, wire_polys, lu_polys = prover_input
        
        # include verifier input into Fiat-Shamir
        h.update(inputs)
        
        L, R, O = self._to_eval_polys(trace, inputs, witness)
        
        Lcmt = self.pcs.commit(L.as_vector())
        Rcmt = self.pcs.commit(R.as_vector())
        Ocmt = self.pcs.commit(O.as_vector())
        cmts = [Lcmt, Rcmt, Ocmt]
        
        h.update_raw(cmts)
        
        T = (L, R, O)
        
        # prove inputs
        print("proving inputs")
        t = cputime()
        prf_inp = self._prove_inputs(ivp, L, inputs, h)
        print(f"Done in {cputime(t)}s")
        
        # prove gate computations
        print("proving gates")
        t = cputime()
        prf_gates = self._prove_gates(selector_polys, T, h)
        print(f"Done in {cputime(t)}s")
        
        # prove wiring
        print("proving wires")
        t = cputime()
        prf_wires = self._prove_wires(wire_polys, T, h)
        print(f"Done in {cputime(t)}s")
        
        if lu_polys != None:
            #prove lookups
            print("proving lookups")
            t = cputime()
            prf_lu = self._prove_lookups(lu_polys, L, h)
            print(f"Done in {cputime(t)}s")
        else:
            prf_lu = None
        
        print("Proving trace poly queries")
        t = cputime()
        T_prfs = []
        for ppoly in T:
            p2o = ppoly.points_to_open
            if p2o:
                outs, prfs = self.pcs.open(ppoly.as_vector(), p2o, h)
                T_prfs.append((OrderedDict(zip(p2o, outs)), prfs))
        
        print(f"Done in {cputime(t)}s")
        
        print(f"Overall proving time: {cputime(t_top)}s")
        return cmts, inputs, prf_inp, prf_gates, prf_wires, prf_lu, T_prfs
        
    def verify(self, verifier_input, prf, h=None):
        print("Verifying proof.")
        t_top = cputime()
        
        F = self.P.base_ring()
        if not h:
            h = Hash(F)
        
        ivp_cmt, selector_cmts, wire_cmts, lu_cmts = verifier_input
        cmts, inps, prf_inp, prf_gates, prf_wires, prf_lu, T_prfs = prf
        Lcmt, Rcmt, Ocmt = cmts
        l_points = T_prfs[0][0]
        r_points = T_prfs[1][0]
        o_points = T_prfs[2][0]
        
        
        h.update(inps)
        h.update_raw(cmts)
        
        # verify input
        print("Verifying inputs")
        t = cputime()
        if not self._verify_inputs(ivp_cmt, Lcmt, inps, prf_inp, l_points, h):
            return False
        print(f"Done in {cputime(t)}s.")
        
        # verify gates
        print("Verifying gates")
        t = cputime()
        if not self._verify_gates(selector_cmts, cmts, prf_gates, l_points, r_points, o_points, h):
            return False
        print(f"Done in {cputime(t)}s.")
        
        # verify wires
        print("Verifying wires")
        t = cputime()
        if not self._verify_wires(wire_cmts, cmts, prf_wires, l_points, r_points, o_points, h):
            return False
        print(f"Done in {cputime(t)}s.")
        
        if lu_cmts != None:
            # verify lookup
            print("Verifying lookups")
            t = cputime()
            if not self._verify_lookups(lu_cmts, Lcmt, prf_lu, l_points, h):
                return False
            print(f"Done in {cputime(t)}s.")
        
        print("Verifying trace polys")
        t = cputime()
        for cmt, query in zip(cmts, T_prfs):
            point_map = query[0]
            prf = query[1]
            if not self.pcs.verify(cmt, self.d, list(point_map.keys()), list(point_map.values()), prf, h):
                print("Openings of trace polys failed.")
                return False
        print(f"Done in {cputime(t)}s.")
        print(f"Overall verification time: {cputime(t_top)}s")
        return True    
    
    def proof_size(self, prf):
        cmt, inps, prf_inp, prf_gates, prf_wires, prf_lu, T_prfs = prf
        cmts_all = []
        queries_all = []
        
        # inputs
        q_cmt, q_prf, ivp_prf, kq = prf_inp
        cmts_all.append(q_cmt)
        queries_all.append(q_prf)
        
        # gates
        cmts, ks, queries = prf_gates
        cmts_all += cmts
        queries_all += queries
        
        # wiring
        cmts, ks, queries = prf_wires
        cmts_all += cmts
        queries_all += queries
        
        # lookup
        if prf_lu != None:
            cmts, queries, _ = prf_lu
            cmts_all += cmts
            queries_all += queries
        
        for point_map, prf in T_prfs:
            queries_all.append((list(point_map.values()), prf))
        
        F_count = 0
        H_count = 3 # 3 for the initial commitment
        
        H_count += len(cmts_all)
        for query in queries_all:
            # ~ print(query)
            H, F = self.pcs.proof_size(query)
            H_count += H
            F_count += F
        
        byts = H_count * 32 + F_count * 8
        
        return H_count, F_count, byts
    
    def test():
        poly_fri = PolyFRI(p, beta, ell)
        plonk = Plonk(poly_fri)
        F = poly_fri.fri.F
        selector_add = {0: 0, 1: 1, 2: 1, 3: 0}
        selector_mul = {0: 0, 1: 0, 2: 0, 3: 1}
        selector_con = {0: 1, 1: 0, 2: 0, 3: 0}
        
        witness = [6]
        inputs = [5, 77]
        trace = [(0, 0, 1),
                (5, 6, 11),
                (6, 1, 7),
                (11, 7, 77)]
        wires = [(-1, 3), (0, 1), (-3, 4, 6), (2, 7), (5, 9), (8, 10), (-2, 11)]
        lu_selector = {-3 : 1 }
        table = [F(-1), F(0), F(6)]
        lookup_data = (lu_selector, table)
        
        pinput, vinput = plonk.preprocess_circuit(4, 2, 1, (selector_add, selector_mul, selector_con), wires, lookup_data)
        
        prf = plonk.prove(pinput, trace, inputs, witness)
        print(f"Circuit parameters: gates: {len(trace)}, inputs: {len(inputs) + len(witness)}, poly degree: {plonk.d}")
        hashes, field_elements, byts = plonk.proof_size(prf)
        print(f"Proof size: {hashes} hash values and {field_elements} field elements resulting in 2^{byts.log(2).n()} bytes")
        assert plonk.verify(vinput, prf), "PLONK verification failed"
