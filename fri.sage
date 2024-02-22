# FRI protocol following ia.cr/2021/582, Section 3.9

RS = codes.ReedSolomonCode

p = 97
F = GF(p)
k = 8
n = 32
C = RS(F, n, k)
omega = C.evaluation_points()[1]

ell = 10

def dumb_hash_ext(lst):
    return reduce(dumb_hash, lst[1:], lst[0])

# TODO: replace with POSEIDON (or something else)
def dumb_hash(left, right):
    return left ** 5 - right

def merkle_commit(lst):
    tree = [list(lst)]
    while len(tree[-1]) > 1:
        tree.append([dumb_hash(left, right) for left, right in zip(tree[-1][::2], tree[-1][1::2])])
    return tree

def merkle_open(tree, index):
    path = [tree[0][index]]
    i = index
    for layer in tree[:-1]:
        sibling = i - 1 if i % 2 else i + 1
        path.append(layer[sibling])
        i //= 2
    return path

def merkle_verify(root, path, index):
    val = path[0]
    i = index
    for node in path[1:]:
        val = dumb_hash(node, val) if i % 2 else dumb_hash(val, node)
        i //= 2
    return val == root

def _fri_commit(pol, k, n, omega, trees=[]):
    if k == 1:
        return trees, pol[0]
    rs = RS(F, n, k, omega)
    code_word = rs(pol)
    # commit to code_word
    tree = merkle_commit(code_word)
    lda = dumb_hash_ext([t[-1][0] for t in trees + [tree]])
    even = vector(F, pol[::2])
    odd = vector(F, pol[1::2])
    return _fri_commit(even + lda * odd, k // 2, n // 2, omega ** 2, trees + [tree])

def _fri_sample(trees, v, n):
    if not trees:
        return []
    path_v = merkle_open(trees[0], v)
    v_neg = (v + n // 2) % n
    path_v_neg = merkle_open(trees[0], v_neg)
    v2 = min(v, v_neg)
    return [(path_v, path_v_neg)] + _fri_sample(trees[1:], v2, n // 2)

def fri_prove(pol):
    trees, pol = _fri_commit(pol, k, n, omega)
    roots = [t[-1][0] for t in trees] + [pol]
    msgs = roots.copy()
    
    queries = []
    for _ in range(ell):
        v = dumb_hash_ext(msgs).lift() % n
        paths = _fri_sample(trees, v, n)
        for level in paths:
            for path in level:
                msgs += path
        queries.append(paths)
    return roots, queries

def _fri_verify(prf, ldas, k, n, omega, v, pv=None):
    roots, paths = prf
    if k == 1:
        if len(roots) != 1:
            print(f"Roots={roots} does not have lenth 1.")
            return False
        return True
    
    path_v, path_v_neg = paths[0]
    root = roots[0]
    rs = RS(F, n, k, omega)
    if pv == None:
        pv = path_v[0]
        if not merkle_verify(root, path_v, v):
            print(f"Merkle verification on v={v} failed.")
            return False
    v_neg = (v + n // 2) % n
    pv_neg = path_v_neg[0]
    if not merkle_verify(root, path_v_neg, v_neg):
        print(f"Merkle verification on v_neg={v_neg} failed.")
        return False
    
    v_ = rs.evaluation_points()[v]
    # pv        == gv2 + v_ * hv2
    # pv_neg    == gv2 - v_ * hv2
    gv2 = (pv + pv_neg) / 2
    hv2 = (pv - pv_neg) / (2 * v_)
    
    p1v2 = gv2 + ldas[0] * hv2
    
    v2 = min(v, v_neg)
    # if k == 2 the next "code word" is actually the constant poly
    p1v2_ = roots[1]
    if k > 2:
        next_root = roots[1]
        next_path_v = paths[1][0]
        p1v2_ = next_path_v[0]
        if not merkle_verify(next_root, next_path_v, v2):
            print(f"Merkle verification on v2={v2} failed.")
            return False
    
    if not p1v2 == p1v2_:
        print("Poly values don't match.")
        return False
    
    return _fri_verify((roots[1:], paths[1:]), ldas[1:], k // 2, n // 2, omega ** 2, v2, p1v2)

def fri_verify(prf):
    roots, queries = prf
    msgs = roots.copy()
    ldas = [dumb_hash_ext(msgs[:i]) for i in range(1, len(roots))]
    
    for query in queries:
        v = dumb_hash_ext(msgs).lift() % n
        if not _fri_verify((roots, query), ldas, k, n, omega, v):
            return False
        for level in query:
            for path in level:
                msgs += path
    return True

def test_fri(iterations):
    for _ in range(iterations):
        prf = fri_prove(vector(F, [F.random_element() for _ in range(k)]))
        assert fri_verify(prf), "FRI verification failed."

def test_merkle(iterations):
    for _ in range(iterations):
        vals = [F.random_element() for _ in range(n)]
        index = randint(0, n - 1)
        tree = merkle_commit(vals)
        root = tree[-1][0]
        prf = merkle_open(tree, index)
        assert merkle_verify(root, prf, index)
