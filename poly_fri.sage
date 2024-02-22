# Poly commitment scheme based on FRI
import hashlib

class Hash:
    """
    This class is a thin wrapper around the hash function SHA256 from hashlib with the ability to take field elements
    as input.
    """
    def __init__(self, F, byte_size=8):
        """
        Constructs a new hash object.

        :param F: the field that the hash function should be able to take as input.
        :param byte_size: the size of field elements in bytes.
        """

        self.F = F
        self.byte_size = byte_size
        self.internal_hash = hashlib.sha256()
    
    def update(self, msg):
        """
        Updates the internal state of the hash function with field elements.

        :param msg: a list of field elements.
        """

        for m in msg:
            self.internal_hash.update(int(m).to_bytes(self.byte_size, 'big', signed=False))
    
    def update_raw(self, msg):
        """
        Updates the internal state of the hash function with raw bytes. Effectively a wrapper around the corresponding
        SHA256 function.

        :param msg: a list of bytes.
        """
        for m in msg:
            self.internal_hash.update(m)
    
    def digest(self):
        """
        Return the current digest of the hash function as field element.

        Note that the output size of the internal hash function is 32 bytes, so the output is truncated
        to self.byte_size to construct a field element.

        :return: a field element respresenting the current digest.
        """
        return self.F(int.from_bytes(self.internal_hash.digest()[:self.byte_size], 'big', signed=False))

# toy field size
# ~ p = 97

# less toy-ish field size
p = 2^64 - 2^32 + 1

# beta is expansion factor of RS code
beta = 4

# number of points to sample for FRI
ell = 32

class Merkle:
    ### Merkle commitments
    def hash_pair(left, right):
        h = hashlib.sha256()
        h.update(left)
        h.update(right)
        return h.digest()
    
    def commit(self, lst):
        tree = [list(lst)]
        while len(tree[-1]) > 1:
            tree.append([Merkle.hash_pair(left, right) for left, right in zip(tree[-1][::2], tree[-1][1::2])])
        return tree

    def open(tree, index):
        path = [tree[0][index]]
        i = index
        for layer in tree[:-1]:
            sibling = i - 1 if i % 2 else i + 1
            path.append(layer[sibling])
            i //= 2
        return path

    def verify(self, root, path, index):
        val = path[0]
        i = index
        for node in path[1:]:
            val = Merkle.hash_pair(node, val) if i % 2 else Merkle.hash_pair(val, node)
            i //= 2
        return val == root

    def test(iterations):
        merkle = Merkle()
        for _ in range(iterations):
            n = 2^10
            vals = [randint(0, 2^64 - 1).to_bytes(8, 'big', signed=False) for _ in range(n)]
            index = randint(0, n - 1)
            tree = merkle.commit(vals)
            root = tree[-1][0]
            prf = Merkle.open(tree, index)
            assert merkle.verify(root, prf, index), "Merkle verification failed."

class FRI:
    ### FRI for (proximity to) low degree testing
    def __init__(self, p, beta, ell):
        self.p = p
        self.F = GF(p)
        self._omega = self.F.multiplicative_generator()
        
        self.merkle = Merkle()
        self.num_bytes = ceil(ceil(p.log(2)) / 8)
        
        self.beta = beta
        self.ell = ell
        
        self.twiddle_dic = {}
        self.coset_dic = {}
        self.eval_dic = {}
        
        self.roots = {}
    
    def F2bytes(self, a):
        return int(a).to_bytes(self.num_bytes, 'big', signed=False) 

    def bytes2F(self, b):
        return self.F(int.from_bytes(b[:self.num_bytes], 'big', signed=False))
    
    def _root_of_unity(self, s):
        if not s in self.roots:
            self.roots[s] = self._omega^( (self.p - 1) // s)
        return self.roots[s]
        
    def _rs_encode(self, pol, n, k, omega, coset):
        if len(pol) == n:
            # evidently, pol is already encoded
            return pol
        elif len(pol) <= k:
            if (n, omega) not in self.twiddle_dic:
                self.twiddle_dic[(n, omega)] = [omega^i for i in range(n)]
            if (k, coset) not in self.coset_dic:
                self.coset_dic[(k, coset)] = [coset^i for i in range(k)]
            twiddles = self.twiddle_dic[(n, omega)]
            cosets = self.coset_dic[(k, coset)]
            return vector(self.F, pari.fft(twiddles, [p * c for p, c in zip(pol, cosets)]))
        else:
            raise ValueError(f"Length of given polynomial is {len(pol)} but should be either less than k={k} or equal to n={n}.")

    def _rs_evaluation_points(self, n, omega, coset):
        if (n, omega, coset) not in self.eval_dic:
            ev_pts = [coset];
            for i in range(1, n):
                ev_pts.append(ev_pts[-1] * omega);
            self.eval_dic[(n, omega, coset)] = ev_pts
        return self.eval_dic[(n, omega, coset)];
    
    def _listify(x):
        return x if isinstance(x, list) else [x]
    
    def _get_codeword(self, k, n, omega, coset, pols, iws, h):
        evals = self._rs_evaluation_points(n, omega, coset)
        codewords = []
        trees = []
        for pol, iw in zip(pols, iws):
            codeword = self._rs_encode(pol, n, k, omega, coset)
            tree = self.merkle.commit([self.F2bytes(c) for c in codeword])
            h.update_raw([tree[-1][0]])
            trees.append(tree)
            for i, w in iw: # This loop is also costly (because of the multi inverse ? or the vector construct ?)
                codewords.append(vector(self.F, [(fi - w) / (evi - i) for fi, evi in zip(codeword, evals)]))
        alpha = h.digest()
        d = len(codewords);
        codeword = codewords[-1];
        for _d in range(d-2,-1,-1):
            codeword *= alpha
            codeword += codewords[_d];
        h.update([self.F(0)])
        return codeword, trees
    
    def _fri_commit(self, codeword, k, n, omega, coset, h, skip_tree=False):
        verbose = 0; # Put to 1 to have precise monitoring
        if k == 1:
            h.update([codeword[0]])
            return [[[codeword[0]]]]

        t = cputime();
        if verbose > 0: print("\t\tcumul rs_encode {}".format(cputime(t)));
        tree = []
        if not skip_tree:
            tree.append(self.merkle.commit([self.F2bytes(c) for c in codeword]))
            if verbose > 0: print("\t\tcumul merkle_commit {}".format(cputime(t)));
            h.update_raw([tree[0][-1][0]])
        if verbose > 0: print("\t\tcumul hupdate {}".format(cputime(t)));    
        evals = self._rs_evaluation_points(n, omega, coset)
        if verbose > 0: print("\t\tcumul evalpts {}".format(cputime(t)));

        lda = h.digest()
        next_k = k // 2 + 1 if k % 2 else k // 2
        lefts = [(lda + ev) * codeword[i] / (2 * ev) for i, ev in enumerate(evals[:n // 2])] # I think lefts/rights might be improvable also
        rights = [(lda - ev) * codeword[i + (n // 2)] / (2 * ev) for i, ev in enumerate(evals[:n // 2])]
        next_cw = [left - right for left, right in zip(lefts, rights)]
        if verbose > 0: print("\tcumul second part {}".format(cputime(t)));
        ret = tree + self._fri_commit(next_cw, next_k, n // 2, omega ** 2, coset ** 2, h)
        return ret;

    def _fri_sample(self, trees, v, n, h, sim_trees=1):
        if not trees:
            return []
        
        paths = []
        for tree in trees[:sim_trees]:
            path_v = Merkle.open(tree, v)
            h.update_raw(path_v)
            v_neg = (v + n // 2) % n
            path_v_neg = Merkle.open(tree, v_neg)
            h.update_raw(path_v_neg)
            paths.append((path_v, path_v_neg))
            
        v2 = min(v, v_neg)
        return paths + self._fri_sample(trees[sim_trees:], v2, n // 2, h)

    def _next_pow_of_2(n):
        return ZZ(2^(ceil(log(n, 2))))

    def _rs_parameters(self, k):
        n = FRI._next_pow_of_2(self.beta * k)
        assert (p - 1) % n == 0, "Field size incompatible with RS code length."
        omega = self._root_of_unity(n)
        return n, omega, self._omega
    
    def prove(self, pols, iws=None, cws=None, h=None):
        if not h:
            h = Hash(self.F)
        pols = FRI._listify(pols)
        cws = FRI._listify(cws)
        k = max([len(pol) for pol in pols])
        n, omega, coset = self._rs_parameters(k)
        pols_ = cws if cws else pols
        if iws:
            codeword, trees = self._get_codeword(k, n, omega, coset, pols_, iws, h)
            skip_tree = True
        elif len(pols) > 1:
            raise RuntimeError("FRI proof: no points but multiple polys. Not sure what to do with that.")
        else:
            codeword = self._rs_encode(pols[0], n, k, omega, coset)
            trees = []
            skip_tree = False
        trees += self._fri_commit(codeword, k, n, omega, coset, h, skip_tree=skip_tree)
        roots = [t[-1][0] for t in trees]
        
        queries = []
        for _ in range(self.ell):
            v = h.digest().lift() % n
            paths = self._fri_sample(trees[:-1], v, n, h, sim_trees=len(pols))
            queries.append(paths)
        return roots, queries
        
    def _fri_verify(self, prf, ldas, k, n, omega, coset, v, pv=None, iws=None, alpha=None):
        roots, paths = prf
        if k == 1 and iws == None:
            if len(roots) != 1:
                print(f"Roots={roots} does not have lenth 1.")
                return False
            return True
        
        evals = self._rs_evaluation_points(n, omega, coset)
        v_ = evals[v]
        
        if iws:
            # if iws is not None, we are in the first level, so pv should be None
            # but alpha should be there
            if alpha == None:
                print("Missing alpha argument for multi point opening.")
                return False
            
            t = len(iws)
            alpha_ = self.F(1)
            pv = self.F(0)
            pv_neg = self.F(0)
            for paths_, root, iw in zip(paths[:t], roots[:t], iws):
                path_v, path_v_neg = paths_
                if not self.merkle.verify(root, path_v, v):
                    print(f"Merkle verification on v={v} failed.")
                    return False
                v_neg = (v + n // 2) % n
                v_neg_ = evals[v_neg]
                if not self.merkle.verify(root, path_v_neg, v_neg):
                    print(f"Merkle verification on v_neg={v_neg} failed.")
                    return False
                
                # simulate access to g through fi to compute g(v) and g(-v)
                pv_ = self.bytes2F(path_v[0])
                pv_neg_ = self.bytes2F(path_v_neg[0])
                for i, w in iw:
                    pv += alpha_ * (pv_ - w) / (v_ - i)
                    pv_neg += alpha_ * (pv_neg_ - w) / (v_neg_ - i)
                    alpha_ *= alpha
        else:
            path_v, path_v_neg = paths[0]
            root = roots[0]
            if pv == None:
                pv = self.bytes2F(path_v[0])
                if not self.merkle.verify(root, path_v, v):
                    print(f"Merkle verification on v={v} failed.")
                    return False
            v_neg = (v + n // 2) % n
            pv_neg = self.bytes2F(path_v_neg[0])
            v_neg_ = evals[v_neg]            
            if not self.merkle.verify(root, path_v_neg, v_neg):
                print(f"Merkle verification on v_neg={v_neg} failed.")
                return False
            t = 1
        
        # pv        == gv2 + v_ * hv2
        # pv_neg    == gv2 - v_ * hv2
        gv2 = (pv + pv_neg) / 2
        hv2 = (pv - pv_neg) / (2 * v_)
        
        p1v2 = gv2 + ldas[0] * hv2
        v2 = min(v, v_neg)
        # if k == 2 the next "codeword" is actually the constant poly
        p1v2_ = roots[t]
        if k > 2:
            next_root = roots[t]
            next_path_v = paths[t][0]
            p1v2_ = self.bytes2F(next_path_v[0])
            if not self.merkle.verify(next_root, next_path_v, v2):
                print(f"Merkle verification on v2={v2} failed.")
                return False
        
        if not p1v2 == p1v2_:
            print(f"Poly values don't match: {p1v2} vs {p1v2_}")
            return False
        next_k = k // 2 + 1 if k % 2 else k// 2
        return self._fri_verify((roots[t:], paths[t:]), ldas[1:], next_k, n // 2, omega ** 2, coset ** 2, v2, p1v2)

    def verify(self, prf, k, iws=None, h=None):
        if not h:
            h = Hash(self.F)
        roots, queries = prf
        # number of batched polynomials
        t = 1
        if iws:
            t = len(iws)
        h.update_raw(roots[:t])
        alpha=None
        if iws:
            alpha = h.digest()
            h.update([self.F(0)])
        ldas = [h.digest()]
        for root in roots[t:-1]:
            h.update_raw([root])
            ldas.append(h.digest())
        h.update([roots[-1]])
        
        n, omega, coset = self._rs_parameters(k)
        for query in queries:
            v = h.digest().lift() % n
            if not self._fri_verify((roots, query), ldas, k, n, omega, coset, v, None, iws, alpha=alpha):
                return False
            for level in query:
                for path in level:
                    h.update_raw(path)
        return True

    def test(iterations, k=8):
        fri = FRI(p, beta, ell)
        for _ in range(iterations):
            prf = fri.prove(vector(fri.F, [fri.F.random_element() for _ in range(k)]))
            assert fri.verify(prf, k), "FRI verification failed."

class PCS:
    def root_of_unity(s):
        raise NotImplementedError("This function should be overwritten!")
    
    def commit(self, pol):
        raise NotImplementedError("This function should be overwritten!")
    
    def open(self, pol, i, h=None):
        raise NotImplementedError("This function should be overwritten!")
    
    def verify(self, cmt, k, i, w, prf, h=None):
        raise NotImplementedError("This function should be overwritten!")
    
    def get_poly_ring(self):
        raise NotImplementedError("This function should be overwritten!")
    
    def get_powers_of_omega(self, n, omega, coset):
        raise NotImplementedError("This function should be overwritten!")
    
    def proof_size(prf):
        raise NotImplementedError("This function should be overwritten!")
    
class PolyFRI(PCS):
    ### FRI based polynomial commitment
    def __init__(self, p, beta, ell):
        self.fri = FRI(p, beta, ell)
        P.<x> = PolynomialRing(self.fri.F)
        self.P = P
        self.codewords = {}
    
    def get_poly_ring(self):
        return self.P
    
    def get_powers_of_omega(self, n, omega):
        return self.fri._rs_evaluation_points(n, omega, 1)
    
    def root_of_unity(self, s):
        return self.fri._root_of_unity(s)
    
    def commit(self, pol):
        fri = self.fri
        k = len(pol)
        if k == 1:
            return fri.F2bytes(pol[0])
        n, omega, coset = fri._rs_parameters(k)
        
        codeword = fri._rs_encode(pol, n, k, omega, coset)
        tree = fri.merkle.commit([fri.F2bytes(c) for c in codeword])
        # store codeword for caching
        self.codewords.update({tuple(pol) : codeword})
        return tree[-1][0]

    def open(self, pol, i, h=None):
        i = FRI._listify(i)
        if len(pol) == 1:
            if len(i) == 1:
                return pol[0], None
            else:
                return [pol[0] for _ in range(len(i))], None
        fpoly = self.P(list(pol))
        w = [fpoly(i_) for i_ in i]
        fv = vector(fpoly) if fpoly else zero_vector(F, 1)
        w_ = w[0] if len(w) == 1 else w
        
        tpol = tuple(pol)
        cw = self.codewords[tpol] if tpol in self.codewords else None
        return w_, self.fri.prove(fv, [list(zip(i, w))], cw, h)

    def verify(self, root, k, i, w, prf, h=None):
        if prf == None:
            # poly is constant
            return self.fri.bytes2F(root) == w
        
        i = FRI._listify(i)
        w = FRI._listify(w)
        
        roots, queries = prf
        
        if root != roots[0]:
            print("poly verify: roots don't match")
            return False
        return self.fri.verify(prf, k, [list(zip(i, w))], h)
    
    def batch_open(self, pols, i_s, h=None):
        # ~ if len(pol) == 1:
            # ~ if len(i) == 1:
                # ~ return pol[0], None
            # ~ else:
                # ~ return [pol[0] for _ in range(len(i))], None
        w_s = []
        vpols = []
        cws = []
        iws = []
        for pol, i in zip(pols, i_s):
            fpoly = self.P(list(pol))
            w = [fpoly(i_) for i_ in i]
            w_s.append(w)
            vpols.append(vector(fpoly) if fpoly else zero_vector(F, 1))
        
            tpol = tuple(pol)
            cws.append(self.codewords[tpol] if tpol in self.codewords else None)
            iws.append(list(zip(i, w)))
        return w_s, self.fri.prove(vpols, iws, cws, h)
    
    def batch_verify(self, roots, k, i_s, w_s, prf, h=None):
        # ~ if prf == None:
            # ~ # poly is constant
            # ~ return self.fri.bytes2F(roots[0]) == w
        
        iws = []
        for i, w in zip(i_s, w_s):
            i = FRI._listify(i)
            w = FRI._listify(w)
            iws.append(list(zip(i, w)))
        
        roots_, queries = prf
        
        if any([root != root_ for root, root_ in zip(roots, roots_)]):
            print("poly verify: roots don't match")
            return False
        return self.fri.verify(prf, k, iws, h)
    
    @staticmethod
    def proof_size(prf):
        w, prf_ = prf
        w = FRI._listify(w)
        if not prf_:
            return 0, len(w)
        roots, queries = prf_
        H_count = len(roots)
        F_count = len(w)
        for query in queries:
            for poly in query:
                for path in poly:
                    H_count += len(path[2:])
                    F_count += 2
        return H_count, F_count

    def test(iterations, k=128, n_points=4):
        poly_fri = PolyFRI(p, beta, ell)
        fri = poly_fri.fri
        F = fri.F
        for _ in range(iterations):
            fpol = vector(F, [F.random_element() for _ in range(k)])
            i = [F.random_element() for _ in range(n_points)]
            # make sure i is not in the evaluation domain
            n, omega, coset = fri._rs_parameters(k)
            while any([i_ in fri._rs_evaluation_points(n, omega, coset) for i_ in i]):
                i = [F.random_element() for _ in range(n_points)]
            print("Committing")
            t = cputime()
            root= poly_fri.commit(fpol)
            print(f"Done in {cputime(t)}s. Opening")
            t = cputime()
            w, prf = poly_fri.open(fpol, i)
            print(f"Done in {cputime(t)}s.")
            assert poly_fri.verify(root, k, i, w, prf), "Poly verification failed."
    
    def test_batch(iterations, k=128, n_polys=3, n_points=4):
        poly_fri = PolyFRI(p, beta, ell)
        fri = poly_fri.fri
        F = fri.F
        for _ in range(iterations):
            polys = []
            i_s = []
            for _ in range(n_polys):
                fpol = vector(F, [F.random_element() for _ in range(k)])
                points = randint(1, n_points)
                i = [F.random_element() for _ in range(points)]
                # make sure i is not in the evaluation domain
                n, omega, coset = fri._rs_parameters(k)
                while any([i_ in fri._rs_evaluation_points(n, omega, coset) for i_ in i]):
                    i = [F.random_element() for _ in range(points)]
                polys.append(fpol)
                i_s.append(i)
            print("Committing")
            t = cputime()
            
            roots = [poly_fri.commit(fpol) for fpol in polys]
            print(f"Done in {cputime(t)}s. Opening")
            t = cputime()
            w_s, prf = poly_fri.batch_open(polys, i_s)
            
            print(f"Done in {cputime(t)}s.")
            assert poly_fri.batch_verify(roots, k, i_s, w_s, prf), "Poly verification failed."
    
    

def test_all_fri(iterations):
    Merkle.test(iterations)
    FRI.test(iterations)
    PolyFRI.test(iterations)
