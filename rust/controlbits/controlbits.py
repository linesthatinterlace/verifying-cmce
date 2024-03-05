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
    for i in range(1, m-1):
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

def X_if(bs):
  return [item for l in [(place << 1) ^ bit for place, bit in enumerate(bs)] for item in (l, l ^ 1)]

def cyclemin_pibar(pi):
    c = range(len(pi))
    p = [pi[x ^ 1] for x in c]
    q = [pi[x] ^ 1 for x in c]
    for _ in range(len(pi).bit_length()) :
        p, q = composeinv(p, q), composeinv(q, p)
        cp = composeinv(c, q)
        c = [min(ci, cip) for (ci, cip) in zip(c, cp)]
    return c

def flm_decomp(pi):
    n = len(pi)
    c = cyclemin_pibar(pi)
    f = [c[j << 1] % 2 for j in range(n >> 1)]
    F = X_if(f)
    piinv = composeinv(range(n), pi)
    Fpi = composeinv(F, piinv)
    l = [Fpi[k << 1] % 2 for k in range(n >> 1)]
    L = X_if(l)
    M = composeinv(Fpi, L)
    return (f, M, l)


def permutation2(c):
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
            low = (above_k << 1) ^ below_k
            up = low ^ (b << k)
            pi[low], pi[up] = pi[up], pi[low]

    return pi

def controlbits_iter(pi_init):
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_init + 1) - 1], where m_init is a positive integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init + 1) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of 2^^m_init * (2*m_init + 1) bits.
    '''

    m_init = len(pi_init).bit_length() - 2
    n_pairs = len(pi_init) >> 1
    control_bits = [None] * ((2*m_init + 1) * n_pairs)

    stack = [(0, pi_init)]
    while stack:

        pos, pi = stack.pop()
        if len(pi) >= 2:

            (first_bits, middle_perm, last_bits) = flm_decomp(pi)

            m = len(pi).bit_length() - 2
            gap = n_pairs >> m
            shift = m << (m_init + 1)

            control_bits[pos : pos + n_pairs : gap] = first_bits
            control_bits[pos + shift : pos + shift + n_pairs : gap] = last_bits

            even_perm = [x >> 1 for x in middle_perm[::2]]
            odd_perm = [x >> 1 for x in middle_perm[1::2]]

            stack.append((pos + n_pairs, even_perm))
            stack.append((pos + n_pairs + gap, odd_perm))

    return control_bits

def controlbits_recur(pi):
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_init + 1) - 1], where m_init is a positive integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init + 1) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of 2^^m_init * (2*m_init + 1) bits.
    '''

    if len(pi) >= 2:
      if len(pi) == 2:
        return [pi[0]]

      (first_bits, middle_perm, last_bits) = flm_decomp(pi)

      even_perm = [x >> 1 for x in middle_perm[0::2]]
      odd_perm = [x >> 1 for x in middle_perm[1::2]]

      even_bits = controlbits_recur(even_perm)
      odd_bits = controlbits_recur(odd_perm)

      return first_bits + [s for s0s1 in zip(even_bits, odd_bits) for s in s0s1] + last_bits