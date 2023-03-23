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


def cyclemin_pibar(m, pi):
    n = 1 << m
    p = [pi[x ^ 1] for x in range(n)]
    q = [pi[x] ^ 1 for x in range(n)]
    c = range(n)
    for _ in range(m):
        p, q = composeinv(p, q), composeinv(q, p)
        cp = composeinv(c, q)
        c = [min(ci, cip) for (ci, cip) in zip(c, cp)]
    return c


def X_if(bs):
    return [x ^ bs[x//2] for x in range(2*len(bs))]


def flm_decomp(m, pi):
    n = 1 << m
    c = cyclemin_pibar(m, pi)
    f = [c[2*j] % 2 for j in range(n//2)]
    F = X_if(f)
    piinv = composeinv(range(n), pi)
    Fpi = composeinv(F, piinv)
    l = [Fpi[2*k] % 2 for k in range(n//2)]
    L = X_if(l)
    M = composeinv(Fpi, L)
    return (f, M, l)


def controlbits_iter(m_init, pi_init):
    '''
      pi_init is a permutation of [0, 1, .., 2^^(m_init) - 1], where m_init is a positive integer.
      We don't perform data validation, but if we did, you would need to check that the values in
      pi_init were 0, 1, ..., 2^^(m_init) - 1, in some order (which implicitly also verifies the
      length).

      The output is a list of (2*m - 1) ** 2^^(m_init - 1) bits.
    '''

    # This quantity recurs multiple times and so it is useful to name it. It is the number of bits
    # which represent the first layer of flips in the control bits representation.
    n_pairs = 1 << (m_init - 1)

    # We initialise our control_bits array. We essentially treat this as write-only (in the sense
    # that we will never read from it) but writes will not occur in linear order.
    control_bits = [None] * ((2*m_init - 1) * n_pairs)

    # We initialise the stack, starting our writing head at 0.
    stack = [(0, m_init, pi_init)]
    while stack:
        # We pop the top of the stack.
        # pos is the current position we are writing to in control_bits.
        # m_curr and pi_curr are the current values of m and pi.
        # m_curr is determinable from pi_curr but it is convenient to store it.
        pos, m_curr, pi_curr = stack.pop()
        # If m_curr == 1 we have reached the base case where we can simply read
        # off the bit. (We could use m_curr == 0 as the base case - the loop body does
        # work for m_curr == 1 - but this is more efficient.)
        if m_curr == 1:
            control_bits[pos] = pi_curr[0]

        elif m_curr > 1:
            # Calculate the first and the last 2^^(m_curr - 1) bits, which
            # represent the outer pair swaps, and the middle that remains,
            # The middle permutation is parity-preserving.
            (first_bits, middle_perm, last_bits) = flm_decomp(m_curr, pi_curr)

            # gap is the space between each bit set. For each layer of the stack,
            # this is twice is large, because an extra interleve of bits occurs to it.
            gap = n_pairs >> (m_curr - 1)

            # shift calculates where we need to start writing the last bits.
            shift = (m_curr - 1) << m_init

            # These two lines place the bits we calculate this time in the right places.
            control_bits[pos: pos + n_pairs: gap] = first_bits
            control_bits[pos + shift: pos + shift + n_pairs: gap] = last_bits

            # We divide the middle perm (which preserves parity) by 2 and get two weaved perms
            # which we then unweave.
            even_perm = [x // 2 for x in middle_perm[::2]]
            odd_perm = [x // 2 for x in middle_perm[1::2]]

            # We add the unweaved perms to the stack, moving the writing head to the right place
            # for each. This process terminates because m_curr is reduced by 1 for both (and it is
            # the "right" value for the new permutation).
            stack.append((pos + n_pairs, m_curr - 1, even_perm))
            stack.append((pos + n_pairs + gap, m_curr - 1, odd_perm))

    return control_bits
