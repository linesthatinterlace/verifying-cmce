import random

def permutation(c):
    m = 1
    while (2*m-1) << (m-1) < len(c):
        m += 1
    assert (2*m-1) << (m-1) == len(c)
    n = 1 << m
    pi = list(range(n))
    for i in range(2*m-1):
        gap = 1 << min(i, 2*m-2-i)
        for j in range(n//2):
            if c[i*n//2+j]:
                pos = (j % gap)+2*gap*(j//gap)
                pi[pos], pi[pos+gap] = pi[pos+gap], pi[pos]
    return pi

def composeinv(c, pi):
    return [y for x, y in sorted(zip(pi, c))]


def controlbits(pi):
    n = len(pi)
    m = 1
    while 1 << m < n:
        m += 1
    assert 1 << m == n
    if m == 1:
        return [pi[0]]
    p = [pi[x ^ 1] for x in range(n)]
    q = [pi[x] ^ 1 for x in range(n)]
    piinv = composeinv(range(n), pi)
    p, q = composeinv(p, q), composeinv(q, p)
    c = [min(x, p[x]) for x in range(n)]
    p, q = composeinv(p, q), composeinv(q, p)
    for _ in range(1, m-1):
        cp, p, q = composeinv(c, q), composeinv(p, q), composeinv(q, p)
        c = [min(c[x], cp[x]) for x in range(n)]
    f = [c[2*j] % 2 for j in range(n//2)]
    F = [x ^ f[x//2] for x in range(n)]
    Fpi = composeinv(F, piinv)
    l = [Fpi[2*k] % 2 for k in range(n//2)]
    L = [y ^ l[y//2] for y in range(n)]
    M = composeinv(Fpi, L)
    subM = [[M[2*j+e]//2 for j in range(n//2)] for e in range(2)]
    subz = map(controlbits, subM)
    z = [s for s0s1 in zip(*subz) for s in s0s1]
    return f+z+l

def permutation_chunks(c):
    '''
      c is a list of 2^^m * (2*m + 1) bits, where m is a nonnegative integer.

      The output is a permutation of [0, 1, .., 2^^(m + 1) - 1] corresponding to the control
      bits represented by c.
    '''

    m = 0
    while (2*m + 1) << m < len(c):
        m += 1
    assert (2*m + 1) << m == len(c)

    pi = list(range(1 << (m + 1)))

    c_chunks = [c[i : i + (1 << m)] for i in range(0, len(c), 1 << m)]
    for i, chunk in enumerate(c_chunks):
        k = min(i, 2*m - i)
        for j, b in enumerate(chunk):
            above_k = (j >> k) << k
            below_k = j ^ above_k
            low = (above_k << 1) | below_k
            up = low | (b << k)
            pi[low], pi[up] = pi[up], pi[low]

    return pi

def x_if_compose_left (bs, cs):
    '''
      bs is a list of bits of length 2^m.
      c is a list of numbers < 2^(m + 1) (that is, whose binary representation has at most m + 1
      bits).

      X_if_compose_left returns the list of such numbers with their last bit flipped according
      to whether the bit that corresponds to the index of bs given by their m most-significant bits
      is set.

      For a cs representing a permutation, this is the same as as multiplication on the left by the
      permutation defined by the bs.
    '''
    return [c ^ bs[c >> 1] for c in cs]

def x_if_compose_right (cs, bs):
    '''
      bs is a list of bits of length k.
      c is a list whose length is 2*k.

      X_if_compose_right returns the same list, with adjacent pairs of elements flipped just when
      the corresponding bit of bs is set.

      For a cs representing a permutation, this is the same as as multiplication on the right by the
      permutation defined by the bs.
    '''
    for p, b in enumerate(bs):
        low = p << 1
        up = low ^ b
        cs[low], cs[up] = cs[up], cs[low]

    return cs

def cyclemin_pibar(pi):
    '''
      Given a permutation pi on 2^k, calculate the minimum member of the cycle corresponding to
      the elements of 0, ... 2^k under the commutator of pi with the xor involution.
    '''
    c = range(len(pi))
    p = [pi[x ^ 1] for x in c]
    q = [x ^ 1 for x in pi]
    for _ in range((len(pi) >> 2).bit_length()):
        p, q = composeinv(p, q), composeinv(q, p)
        cp = composeinv(c, q)
        c = [min(ci, cip) for (ci, cip) in zip(c, cp)]

    return c

def flm_decomp(pi):
    '''
      Decompose a permutation pi on 2^^(k + 1) elements into a permutation m on 2^(k + 1) elements
      which preserves parity, and two bitstrings f and l which represent conditional xor
      permutations F and L such that pi = F * m * L.
    '''
    cs = cyclemin_pibar(pi)
    f = [c & 1 for c in cs[::2]]
    fpi = x_if_compose_left(f, pi)
    l = [k & 1 for k in fpi[::2]]
    m = x_if_compose_right(fpi, l)
    return (f, m, l)

def controlbits_iter(pi_init : "list[int]") -> "list[int]":
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_init + 1) - 1], where m_init is a nonnegative
      integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init + 1) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of 2^^m_init * (2*m_init + 1) bits.
    '''

    m_init = len(pi_init).bit_length() - 2
    n_pairs = len(pi_init) >> 1
    control_bits = [-1] * ((2*m_init + 1) * n_pairs)

    stack = [(0, pi_init)]
    while stack:

        pos, pi = stack.pop()
        m = len(pi).bit_length() - 2
        if m >= 0:
            if m == 0:
                control_bits[pos] = pi[0]
            else:
                (first_bits, middle_perm, last_bits) = flm_decomp(pi)

                gap = 1 << (m_init - m)

                for i, (fb, lb) in enumerate(zip(first_bits, last_bits)):
                    control_bits[pos + gap*i] = fb
                    control_bits[pos + gap*i + (m << (m_init + 1))] = lb

                middle_perm = [x >> 1 for x in middle_perm]

                stack.append((pos + n_pairs + gap, middle_perm[1::2]))
                stack.append((pos + n_pairs, middle_perm[::2]))

    return control_bits

def controlbits_recur(pi : "list[int]") -> "list[int]":
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_ init + 1) - 1], where m_init is a positive
      integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init + 1) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of 2^^m_init * (2*m_init + 1) bits.
    '''
    control_bits = []
    if len(pi) >= 2:
        if len(pi) == 2:
            control_bits = [pi[0]]
        else:
            (first_bits, middle_perm, last_bits) = flm_decomp(pi)
            middle_perm = [x >> 1 for x in middle_perm]
            even_perm = middle_perm[0::2]
            odd_perm = middle_perm[1::2]

            even_bits = controlbits_recur(even_perm)
            odd_bits = controlbits_recur(odd_perm)

            middle_bits = [s for s0s1 in zip(even_bits, odd_bits) for s in s0s1]

            control_bits = first_bits + middle_bits + last_bits
    return control_bits

def getbit(i, k):
    return (((k >> (i + 1)) << (i + 1)) ^ k) >> i

def getres(i, k):
    top_bits = (k >> (i + 1)) << (i + 1)
    bottom_bits = ((k ^ top_bits) | (1 << i)) ^ (1 << i)
    return (top_bits >> 1) | bottom_bits

def mergebitres(i, k, b):
    top_bits = (k >> i) << i

    k = (top_bits << 1) | (k ^ top_bits)
    return k | (b << i)

def x_if_compose_left_extended(i, bs, cs):
    return [mergebitres(i, r, bs[r] ^ getbit(i, c)) for c in cs for r in [getres(i, c)]]

def x_if_compose_right_extended(i, cs, bs):

    cs = [c for c in cs]
    for p, b in enumerate(bs):
        low = mergebitres(i,p,0)
        up = mergebitres(i,p,b)
        cs[low], cs[up] = cs[up], cs[low]

    return cs

def xbxf_extended(i : int, pi):
    c = range(len(pi))
    return [pi[x ^ (1 << i)] for x in c]

def cyclemin_pibar_extended(i : int, pi : "list[int]"):
    '''
      Given a permutation pi on 2^k, calculate the minimum member of the cycle corresponding to
      the elements of 0, ... 2^k under the commutator of pi with the xor involution.
    '''
    c = range(len(pi))
    p = [pi[x ^ (1 << i)] for x in c]
    q = [x ^ (1 << i) for x in pi]
    for _ in range((len(pi) >> 2).bit_length() - i):
        p, q = composeinv(p, q), composeinv(q, p)
        cp = composeinv(c, q)
        c = [min(ci, cip) for (ci, cip) in zip(c, cp)]

    return c

def flm_decomp_extended(t : int, pi : "list[int]"):
    '''
      Decompose a permutation pi on 2^^(k + 1) elements into a permutation m on 2^(k + 1) elements
      which preserves parity, and two bitstrings f and l which represent conditional xor
      permutations F and L such that pi = F * m * L.
    '''
    cs = cyclemin_pibar_extended(t, pi)
    f = [getbit(t, c) for i, c in enumerate(cs) if getbit(t, i) == 0]
    fpi = x_if_compose_left_extended(t, f, pi)
    l = [getbit(t, k) for i, k in enumerate(fpi) if getbit(t, i) == 0]
    m = x_if_compose_right_extended(t, fpi, l)
    return (f, m, l)

def final_bits(pi : "list[int]"):
    '''
      Decompose a permutation pi on 2^^(k + 1) elements into a permutation m on 2^(k + 1) elements
      which preserves parity, and two bitstrings f and l which represent conditional xor
      permutations F and L such that pi = F * m * L.
    '''
    return [int(k != t) for k, t in enumerate(pi[:len(pi)//2])]

def controlbits_extended(pi : "list[int]") -> "list[int]":
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_ init + 1) - 1], where m_init is a positive
      integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init + 1) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of 2^^m_init * (2*m_init + 1) bits.
    '''
    m = (len(pi) >> 2).bit_length()
    return controlbits_extended_aux(0, m, pi)

def controlbits_extended_aux(i : int, m : int, pi : "list[int]") -> "list[int]":
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_ init + 1) - 1], where m_init is a positive
      integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init + 1) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of 2^^m_init * (2*m_init + 1) bits.
    '''
    (first_bits, middle_perm, last_bits) = flm_decomp_extended(i, pi)
    if i >= m:
      return last_bits
    return first_bits + controlbits_extended_aux(i + 1, m, middle_perm) + last_bits

def controlbits_loop(pi : "list[int]") -> "list[int]":
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_ init + 1) - 1], where m_init is a positive
      integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init + 1) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of 2^^m_init * (2*m_init + 1) bits.
    '''
    m = (len(pi) >> 2).bit_length()
    first_bits = []
    last_bits = []
    for i in range(m):
        (left_layer, pi, right_layer) = flm_decomp_extended(i, pi)
        first_bits = first_bits + left_layer
        last_bits = right_layer + last_bits
    right_layer = final_bits(pi)
    last_bits = right_layer + last_bits
    return first_bits + last_bits

def controlbits_tailrecursive(pi : "list[int]") -> "list[int]":
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_ init + 1) - 1], where m_init is a positive
      integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init + 1) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of 2^^m_init * (2*m_init + 1) bits.
    '''
    return controlbits_tailrecursive_aux(0, pi, [], [])


def controlbits_tailrecursive_aux(i : int, pi : "list[int]", first_bits : "list[int]", last_bits : "list[int]") -> "list[int]":
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_ init + 1) - 1], where m_init is a positive
      integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init + 1) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of 2^^m_init * (2*m_init + 1) bits.
    '''
    (left_layer, middle_perm, right_layer) = flm_decomp_extended(i, pi)
    m = (len(pi) >> 2).bit_length()
    if i >= m:
      return first_bits + right_layer + last_bits
    return controlbits_tailrecursive_aux(i + 1, middle_perm, first_bits + left_layer, right_layer + last_bits)

def random_control_bits(n):
    return [random.getrandbits(1) for _ in range((2*n + 1) << n )]

def test_random_control_bits(n, test_num):
    fail = 0
    for _ in range(test_num):
        cb = random_control_bits(n)
        p = permutation(cb)
        cb2 = controlbits_recur(p)
        p2 = permutation(cb2)
        if p != p2:
            fail += 1
    successes = test_num - fail
    print(f"Tested {test_num} times with size parameter {n}")
    print(f"Failures: {fail}")
    print(f"Successes: {successes}")

def test_random_control_bits_extended(n, test_num):
    fail = 0
    for _ in range(test_num):
        cb = random_control_bits(n)
        p = permutation(cb)
        cb2 = controlbits_extended(p)
        p2 = permutation(cb2)
        if p != p2:
            fail += 1
    successes = test_num - fail
    print(f"Tested {test_num} times with size parameter {n}")
    print(f"Failures: {fail}")
    print(f"Successes: {successes}")