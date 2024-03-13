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
