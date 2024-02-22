
def prod_tree(elts):
    _n = len(elts)
    if _n == 1:
        return elts

    _half   = _n//2
    _l_tree = prod_tree(elts[:_half])
    _r_tree = prod_tree(elts[_half:])
    _root   = _l_tree[0] * _r_tree[0]
    return [_root, _l_tree, _r_tree]


# Multi-inverses using a variant of Montgomery's trick
def _internal_multi_inverse(i_tree):
    if len(i_tree) == 1:
        return i_tree
    il_tree = [ i_tree[0]*i_tree[2][0] ] + i_tree[1][1:] # 2nd terms might also be empty
    ir_tree = [ i_tree[0]*i_tree[1][0] ] + i_tree[2][1:]
    return _internal_multi_inverse(il_tree) + _internal_multi_inverse(ir_tree)

# if elts_tree = prod_tree(elts) is given, it is not recomputed
def multi_inverse(elts, elts_tree=[]):
    if (len(elts_tree) == 0):
        elts_tree = prod_tree(elts)
    i_tree = [ 1/elts_tree[0] ] + elts_tree[1:] # 2nd term might be empty (syntax avoids out of range errors)

    return _internal_multi_inverse(i_tree)


def multi_eval(pols, ev_tree):
    pols_mod = [ _f.mod(ev_tree[0]) for _f in pols ]
    if (len(ev_tree) == 1):
        return [[ _e.constant_coefficient() for _e in pols_mod ]] # Very bizarrely this takes time
    else:
        return multi_eval(pols_mod, ev_tree[1]) + multi_eval(pols_mod, ev_tree[2])

