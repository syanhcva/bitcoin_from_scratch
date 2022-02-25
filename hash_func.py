def gen_sha256_with_variable_scope_protector_to_not_pollute_global_namespace():

    """
    SHA256 implementation.

    Follows the FIPS PUB 180-4 description for calculating SHA-256 hash function
    https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

    Noone in their right mind should use this for any serious reason. This was written
    purely for educational purposes.
    """

    import math
    from itertools import count, islice

    # -----------------------------------------------------------------------------
    # SHA-256 Functions, defined in Section 4

    def rotr(x, n, size=32):
        return (x >> n) | (x << size - n) & (2**size - 1)

    def shr(x, n):
        return x >> n

    def sig0(x):
        return rotr(x, 7) ^ rotr(x, 18) ^ shr(x, 3)

    def sig1(x):
        return rotr(x, 17) ^ rotr(x, 19) ^ shr(x, 10)

    def capsig0(x):
        return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22)

    def capsig1(x):
        return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25)

    def ch(x, y, z):
        return (x & y)^ (~x & z)

    def maj(x, y, z):
        return (x & y) ^ (x & z) ^ (y & z)

    def b2i(b):
        return int.from_bytes(b, 'big')

    def i2b(i):
        return i.to_bytes(4, 'big')

    # -----------------------------------------------------------------------------
    # SHA-256 Constants

    def is_prime(n):
        return not any(f for f in range(2,int(math.sqrt(n))+1) if n%f == 0)

    def first_n_primes(n):
        return islice(filter(is_prime, count(start=2)), n)

    def frac_bin(f, n=32):
        """ return the first n bits of fractional part of float f """
        f -= math.floor(f) # get only the fractional part
        f *= 2**n # shift left
        f = int(f) # truncate the rest of the fractional content
        return f

    def genK():
        """
        Follows Section 4.2.2 to generate K

        The first 32 bits of the fractional parts of the cube roots of the first
        64 prime numbers:

        428a2f98 71374491 b5c0fbcf e9b5dba5 3956c25b 59f111f1 923f82a4 ab1c5ed5
        d807aa98 12835b01 243185be 550c7dc3 72be5d74 80deb1fe 9bdc06a7 c19bf174
        e49b69c1 efbe4786 0fc19dc6 240ca1cc 2de92c6f 4a7484aa 5cb0a9dc 76f988da
        983e5152 a831c66d b00327c8 bf597fc7 c6e00bf3 d5a79147 06ca6351 14292967
        27b70a85 2e1b2138 4d2c6dfc 53380d13 650a7354 766a0abb 81c2c92e 92722c85
        a2bfe8a1 a81a664b c24b8b70 c76c51a3 d192e819 d6990624 f40e3585 106aa070
        19a4c116 1e376c08 2748774c 34b0bcb5 391c0cb3 4ed8aa4a 5b9cca4f 682e6ff3
        748f82ee 78a5636f 84c87814 8cc70208 90befffa a4506ceb bef9a3f7 c67178f2
        """
        return [frac_bin(p ** (1/3.0)) for p in first_n_primes(64)]

    def genH():
        """
        Follows Section 5.3.3 to generate the initial hash value H^0

        The first 32 bits of the fractional parts of the square roots of
        the first 8 prime numbers.

        6a09e667 bb67ae85 3c6ef372 a54ff53a 9b05688c 510e527f 1f83d9ab 5be0cd19
        """
        return [frac_bin(p ** (1/2.0)) for p in first_n_primes(8)]

    # -----------------------------------------------------------------------------

    def pad(b):
        """ Follows Section 5.1: Padding the message """
        b = bytearray(b) # convert to a mutable equivalent
        l = len(b) * 8 # note: len returns number of bytes not bits

        # append but "1" to the end of the message
        b.append(0b10000000) # appending 10000000 in binary (=128 in decimal)

        # follow by k zero bits, where k is the smallest non-negative solution to
        # l + 1 + k = 448 mod 512
        # i.e. pad with zeros until we reach 448 (mod 512)
        while (len(b)*8) % 512 != 448:
            b.append(0x00)

        # the last 64-bit block is the length l of the original message
        # expressed in binary (big endian)
        b.extend(l.to_bytes(8, 'big'))

        return b

    def sha256(b: bytes) -> bytes:

        # Section 4.2
        K = genK()

        # Section 5: Preprocessing
        # Section 5.1: Pad the message
        b = pad(b)
        # Section 5.2: Separate the message into blocks of 512 bits (64 bytes)
        blocks = [b[i:i+64] for i in range(0, len(b), 64)]

        # for each message block M^1 ... M^N
        H = genH() # Section 5.3

        # Section 6
        for M in blocks: # each block is a 64-entry array of 8-bit bytes

            # 1. Prepare the message schedule, a 64-entry array of 32-bit words
            W = []
            for t in range(64):
                if t <= 15:
                    # the first 16 words are just a copy of the block
                    W.append(bytes(M[t*4:t*4+4]))
                else:
                    term1 = sig1(b2i(W[t-2]))
                    term2 = b2i(W[t-7])
                    term3 = sig0(b2i(W[t-15]))
                    term4 = b2i(W[t-16])
                    total = (term1 + term2 + term3 + term4) % 2**32
                    W.append(i2b(total))

            # 2. Initialize the 8 working variables a,b,c,d,e,f,g,h with prev hash value
            a, b, c, d, e, f, g, h = H

            # 3.
            for t in range(64):
                T1 = (h + capsig1(e) + ch(e, f, g) + K[t] + b2i(W[t])) % 2**32
                T2 = (capsig0(a) + maj(a, b, c)) % 2**32
                h = g
                g = f
                f = e
                e = (d + T1) % 2**32
                d = c
                c = b
                b = a
                a = (T1 + T2) % 2**32

            # 4. Compute the i-th intermediate hash value H^i
            delta = [a, b, c, d, e, f, g, h]
            H = [(i1 + i2) % 2**32 for i1, i2 in zip(H, delta)]

        return b''.join(i2b(i) for i in H)

    return sha256
def gen_ripemd160_with_variable_scope_protector_to_not_pollute_global_namespace():

    import sys
    import struct

    # -----------------------------------------------------------------------------
    # public interface

    def ripemd160(b: bytes) -> bytes:
        """ simple wrapper for a simpler API to this hash function, just bytes to bytes """
        ctx = RMDContext()
        RMD160Update(ctx, b, len(b))
        digest = RMD160Final(ctx)
        return digest

    # -----------------------------------------------------------------------------

    class RMDContext:
        def __init__(self):
            self.state = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0] # uint32
            self.count = 0 # uint64
            self.buffer = [0]*64 # uchar

    def RMD160Update(ctx, inp, inplen):
        have = int((ctx.count // 8) % 64)
        inplen = int(inplen)
        need = 64 - have
        ctx.count += 8 * inplen
        off = 0
        if inplen >= need:
            if have:
                for i in range(need):
                    ctx.buffer[have+i] = inp[i]
                RMD160Transform(ctx.state, ctx.buffer)
                off = need
                have = 0
            while off + 64 <= inplen:
                RMD160Transform(ctx.state, inp[off:])
                off += 64
        if off < inplen:
            for i in range(inplen - off):
                ctx.buffer[have+i] = inp[off+i]

    def RMD160Final(ctx):
        size = struct.pack("<Q", ctx.count)
        padlen = 64 - ((ctx.count // 8) % 64)
        if padlen < 1 + 8:
            padlen += 64
        RMD160Update(ctx, PADDING, padlen-8)
        RMD160Update(ctx, size, 8)
        return struct.pack("<5L", *ctx.state)

    # -----------------------------------------------------------------------------

    K0 = 0x00000000
    K1 = 0x5A827999
    K2 = 0x6ED9EBA1
    K3 = 0x8F1BBCDC
    K4 = 0xA953FD4E
    KK0 = 0x50A28BE6
    KK1 = 0x5C4DD124
    KK2 = 0x6D703EF3
    KK3 = 0x7A6D76E9
    KK4 = 0x00000000

    PADDING = [0x80] + [0]*63

    def ROL(n, x):
        return ((x << n) & 0xffffffff) | (x >> (32 - n))

    def F0(x, y, z):
        return x ^ y ^ z

    def F1(x, y, z):
        return (x & y) | (((~x) % 0x100000000) & z)

    def F2(x, y, z):
        return (x | ((~y) % 0x100000000)) ^ z

    def F3(x, y, z):
        return (x & z) | (((~z) % 0x100000000) & y)

    def F4(x, y, z):
        return x ^ (y | ((~z) % 0x100000000))

    def R(a, b, c, d, e, Fj, Kj, sj, rj, X):
        a = ROL(sj, (a + Fj(b, c, d) + X[rj] + Kj) % 0x100000000) + e
        c = ROL(10, c)
        return a % 0x100000000, c

    def RMD160Transform(state, block): #uint32 state[5], uchar block[64]

        x = [0]*16
        assert sys.byteorder == 'little', "Only little endian is supported atm for RIPEMD160"
        x = struct.unpack('<16L', bytes(block[0:64]))

        a = state[0]
        b = state[1]
        c = state[2]
        d = state[3]
        e = state[4]

        #/* Round 1 */
        a, c = R(a, b, c, d, e, F0, K0, 11,  0, x)
        e, b = R(e, a, b, c, d, F0, K0, 14,  1, x)
        d, a = R(d, e, a, b, c, F0, K0, 15,  2, x)
        c, e = R(c, d, e, a, b, F0, K0, 12,  3, x)
        b, d = R(b, c, d, e, a, F0, K0,  5,  4, x)
        a, c = R(a, b, c, d, e, F0, K0,  8,  5, x)
        e, b = R(e, a, b, c, d, F0, K0,  7,  6, x)
        d, a = R(d, e, a, b, c, F0, K0,  9,  7, x)
        c, e = R(c, d, e, a, b, F0, K0, 11,  8, x)
        b, d = R(b, c, d, e, a, F0, K0, 13,  9, x)
        a, c = R(a, b, c, d, e, F0, K0, 14, 10, x)
        e, b = R(e, a, b, c, d, F0, K0, 15, 11, x)
        d, a = R(d, e, a, b, c, F0, K0,  6, 12, x)
        c, e = R(c, d, e, a, b, F0, K0,  7, 13, x)
        b, d = R(b, c, d, e, a, F0, K0,  9, 14, x)
        a, c = R(a, b, c, d, e, F0, K0,  8, 15, x) #/* #15 */
        #/* Round 2 */
        e, b = R(e, a, b, c, d, F1, K1,  7,  7, x)
        d, a = R(d, e, a, b, c, F1, K1,  6,  4, x)
        c, e = R(c, d, e, a, b, F1, K1,  8, 13, x)
        b, d = R(b, c, d, e, a, F1, K1, 13,  1, x)
        a, c = R(a, b, c, d, e, F1, K1, 11, 10, x)
        e, b = R(e, a, b, c, d, F1, K1,  9,  6, x)
        d, a = R(d, e, a, b, c, F1, K1,  7, 15, x)
        c, e = R(c, d, e, a, b, F1, K1, 15,  3, x)
        b, d = R(b, c, d, e, a, F1, K1,  7, 12, x)
        a, c = R(a, b, c, d, e, F1, K1, 12,  0, x)
        e, b = R(e, a, b, c, d, F1, K1, 15,  9, x)
        d, a = R(d, e, a, b, c, F1, K1,  9,  5, x)
        c, e = R(c, d, e, a, b, F1, K1, 11,  2, x)
        b, d = R(b, c, d, e, a, F1, K1,  7, 14, x)
        a, c = R(a, b, c, d, e, F1, K1, 13, 11, x)
        e, b = R(e, a, b, c, d, F1, K1, 12,  8, x) #/* #31 */
        #/* Round 3 */
        d, a = R(d, e, a, b, c, F2, K2, 11,  3, x)
        c, e = R(c, d, e, a, b, F2, K2, 13, 10, x)
        b, d = R(b, c, d, e, a, F2, K2,  6, 14, x)
        a, c = R(a, b, c, d, e, F2, K2,  7,  4, x)
        e, b = R(e, a, b, c, d, F2, K2, 14,  9, x)
        d, a = R(d, e, a, b, c, F2, K2,  9, 15, x)
        c, e = R(c, d, e, a, b, F2, K2, 13,  8, x)
        b, d = R(b, c, d, e, a, F2, K2, 15,  1, x)
        a, c = R(a, b, c, d, e, F2, K2, 14,  2, x)
        e, b = R(e, a, b, c, d, F2, K2,  8,  7, x)
        d, a = R(d, e, a, b, c, F2, K2, 13,  0, x)
        c, e = R(c, d, e, a, b, F2, K2,  6,  6, x)
        b, d = R(b, c, d, e, a, F2, K2,  5, 13, x)
        a, c = R(a, b, c, d, e, F2, K2, 12, 11, x)
        e, b = R(e, a, b, c, d, F2, K2,  7,  5, x)
        d, a = R(d, e, a, b, c, F2, K2,  5, 12, x) #/* #47 */
        #/* Round 4 */
        c, e = R(c, d, e, a, b, F3, K3, 11,  1, x)
        b, d = R(b, c, d, e, a, F3, K3, 12,  9, x)
        a, c = R(a, b, c, d, e, F3, K3, 14, 11, x)
        e, b = R(e, a, b, c, d, F3, K3, 15, 10, x)
        d, a = R(d, e, a, b, c, F3, K3, 14,  0, x)
        c, e = R(c, d, e, a, b, F3, K3, 15,  8, x)
        b, d = R(b, c, d, e, a, F3, K3,  9, 12, x)
        a, c = R(a, b, c, d, e, F3, K3,  8,  4, x)
        e, b = R(e, a, b, c, d, F3, K3,  9, 13, x)
        d, a = R(d, e, a, b, c, F3, K3, 14,  3, x)
        c, e = R(c, d, e, a, b, F3, K3,  5,  7, x)
        b, d = R(b, c, d, e, a, F3, K3,  6, 15, x)
        a, c = R(a, b, c, d, e, F3, K3,  8, 14, x)
        e, b = R(e, a, b, c, d, F3, K3,  6,  5, x)
        d, a = R(d, e, a, b, c, F3, K3,  5,  6, x)
        c, e = R(c, d, e, a, b, F3, K3, 12,  2, x) #/* #63 */
        #/* Round 5 */
        b, d = R(b, c, d, e, a, F4, K4,  9,  4, x)
        a, c = R(a, b, c, d, e, F4, K4, 15,  0, x)
        e, b = R(e, a, b, c, d, F4, K4,  5,  5, x)
        d, a = R(d, e, a, b, c, F4, K4, 11,  9, x)
        c, e = R(c, d, e, a, b, F4, K4,  6,  7, x)
        b, d = R(b, c, d, e, a, F4, K4,  8, 12, x)
        a, c = R(a, b, c, d, e, F4, K4, 13,  2, x)
        e, b = R(e, a, b, c, d, F4, K4, 12, 10, x)
        d, a = R(d, e, a, b, c, F4, K4,  5, 14, x)
        c, e = R(c, d, e, a, b, F4, K4, 12,  1, x)
        b, d = R(b, c, d, e, a, F4, K4, 13,  3, x)
        a, c = R(a, b, c, d, e, F4, K4, 14,  8, x)
        e, b = R(e, a, b, c, d, F4, K4, 11, 11, x)
        d, a = R(d, e, a, b, c, F4, K4,  8,  6, x)
        c, e = R(c, d, e, a, b, F4, K4,  5, 15, x)
        b, d = R(b, c, d, e, a, F4, K4,  6, 13, x) #/* #79 */

        aa = a
        bb = b
        cc = c
        dd = d
        ee = e

        a = state[0]
        b = state[1]
        c = state[2]
        d = state[3]
        e = state[4]

        #/* Parallel round 1 */
        a, c = R(a, b, c, d, e, F4, KK0,  8,  5, x)
        e, b = R(e, a, b, c, d, F4, KK0,  9, 14, x)
        d, a = R(d, e, a, b, c, F4, KK0,  9,  7, x)
        c, e = R(c, d, e, a, b, F4, KK0, 11,  0, x)
        b, d = R(b, c, d, e, a, F4, KK0, 13,  9, x)
        a, c = R(a, b, c, d, e, F4, KK0, 15,  2, x)
        e, b = R(e, a, b, c, d, F4, KK0, 15, 11, x)
        d, a = R(d, e, a, b, c, F4, KK0,  5,  4, x)
        c, e = R(c, d, e, a, b, F4, KK0,  7, 13, x)
        b, d = R(b, c, d, e, a, F4, KK0,  7,  6, x)
        a, c = R(a, b, c, d, e, F4, KK0,  8, 15, x)
        e, b = R(e, a, b, c, d, F4, KK0, 11,  8, x)
        d, a = R(d, e, a, b, c, F4, KK0, 14,  1, x)
        c, e = R(c, d, e, a, b, F4, KK0, 14, 10, x)
        b, d = R(b, c, d, e, a, F4, KK0, 12,  3, x)
        a, c = R(a, b, c, d, e, F4, KK0,  6, 12, x) #/* #15 */
        #/* Parallel round 2 */
        e, b = R(e, a, b, c, d, F3, KK1,  9,  6, x)
        d, a = R(d, e, a, b, c, F3, KK1, 13, 11, x)
        c, e = R(c, d, e, a, b, F3, KK1, 15,  3, x)
        b, d = R(b, c, d, e, a, F3, KK1,  7,  7, x)
        a, c = R(a, b, c, d, e, F3, KK1, 12,  0, x)
        e, b = R(e, a, b, c, d, F3, KK1,  8, 13, x)
        d, a = R(d, e, a, b, c, F3, KK1,  9,  5, x)
        c, e = R(c, d, e, a, b, F3, KK1, 11, 10, x)
        b, d = R(b, c, d, e, a, F3, KK1,  7, 14, x)
        a, c = R(a, b, c, d, e, F3, KK1,  7, 15, x)
        e, b = R(e, a, b, c, d, F3, KK1, 12,  8, x)
        d, a = R(d, e, a, b, c, F3, KK1,  7, 12, x)
        c, e = R(c, d, e, a, b, F3, KK1,  6,  4, x)
        b, d = R(b, c, d, e, a, F3, KK1, 15,  9, x)
        a, c = R(a, b, c, d, e, F3, KK1, 13,  1, x)
        e, b = R(e, a, b, c, d, F3, KK1, 11,  2, x) #/* #31 */
        #/* Parallel round 3 */
        d, a = R(d, e, a, b, c, F2, KK2,  9, 15, x)
        c, e = R(c, d, e, a, b, F2, KK2,  7,  5, x)
        b, d = R(b, c, d, e, a, F2, KK2, 15,  1, x)
        a, c = R(a, b, c, d, e, F2, KK2, 11,  3, x)
        e, b = R(e, a, b, c, d, F2, KK2,  8,  7, x)
        d, a = R(d, e, a, b, c, F2, KK2,  6, 14, x)
        c, e = R(c, d, e, a, b, F2, KK2,  6,  6, x)
        b, d = R(b, c, d, e, a, F2, KK2, 14,  9, x)
        a, c = R(a, b, c, d, e, F2, KK2, 12, 11, x)
        e, b = R(e, a, b, c, d, F2, KK2, 13,  8, x)
        d, a = R(d, e, a, b, c, F2, KK2,  5, 12, x)
        c, e = R(c, d, e, a, b, F2, KK2, 14,  2, x)
        b, d = R(b, c, d, e, a, F2, KK2, 13, 10, x)
        a, c = R(a, b, c, d, e, F2, KK2, 13,  0, x)
        e, b = R(e, a, b, c, d, F2, KK2,  7,  4, x)
        d, a = R(d, e, a, b, c, F2, KK2,  5, 13, x) #/* #47 */
        #/* Parallel round 4 */
        c, e = R(c, d, e, a, b, F1, KK3, 15,  8, x)
        b, d = R(b, c, d, e, a, F1, KK3,  5,  6, x)
        a, c = R(a, b, c, d, e, F1, KK3,  8,  4, x)
        e, b = R(e, a, b, c, d, F1, KK3, 11,  1, x)
        d, a = R(d, e, a, b, c, F1, KK3, 14,  3, x)
        c, e = R(c, d, e, a, b, F1, KK3, 14, 11, x)
        b, d = R(b, c, d, e, a, F1, KK3,  6, 15, x)
        a, c = R(a, b, c, d, e, F1, KK3, 14,  0, x)
        e, b = R(e, a, b, c, d, F1, KK3,  6,  5, x)
        d, a = R(d, e, a, b, c, F1, KK3,  9, 12, x)
        c, e = R(c, d, e, a, b, F1, KK3, 12,  2, x)
        b, d = R(b, c, d, e, a, F1, KK3,  9, 13, x)
        a, c = R(a, b, c, d, e, F1, KK3, 12,  9, x)
        e, b = R(e, a, b, c, d, F1, KK3,  5,  7, x)
        d, a = R(d, e, a, b, c, F1, KK3, 15, 10, x)
        c, e = R(c, d, e, a, b, F1, KK3,  8, 14, x) #/* #63 */
        #/* Parallel round 5 */
        b, d = R(b, c, d, e, a, F0, KK4,  8, 12, x)
        a, c = R(a, b, c, d, e, F0, KK4,  5, 15, x)
        e, b = R(e, a, b, c, d, F0, KK4, 12, 10, x)
        d, a = R(d, e, a, b, c, F0, KK4,  9,  4, x)
        c, e = R(c, d, e, a, b, F0, KK4, 12,  1, x)
        b, d = R(b, c, d, e, a, F0, KK4,  5,  5, x)
        a, c = R(a, b, c, d, e, F0, KK4, 14,  8, x)
        e, b = R(e, a, b, c, d, F0, KK4,  6,  7, x)
        d, a = R(d, e, a, b, c, F0, KK4,  8,  6, x)
        c, e = R(c, d, e, a, b, F0, KK4, 13,  2, x)
        b, d = R(b, c, d, e, a, F0, KK4,  6, 13, x)
        a, c = R(a, b, c, d, e, F0, KK4,  5, 14, x)
        e, b = R(e, a, b, c, d, F0, KK4, 15,  0, x)
        d, a = R(d, e, a, b, c, F0, KK4, 13,  3, x)
        c, e = R(c, d, e, a, b, F0, KK4, 11,  9, x)
        b, d = R(b, c, d, e, a, F0, KK4, 11, 11, x) #/* #79 */

        t = (state[1] + cc + d) % 0x100000000
        state[1] = (state[2] + dd + e) % 0x100000000
        state[2] = (state[3] + ee + a) % 0x100000000
        state[3] = (state[4] + aa + b) % 0x100000000
        state[4] = (state[0] + bb + c) % 0x100000000
        state[0] = t % 0x100000000

    return ripemd160

if __name__ == "__main__":
    sha256 = gen_sha256_with_variable_scope_protector_to_not_pollute_global_namespace()
    print("verify empty hash:",
          sha256(b'').hex())  # should be e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
    print(sha256(b'here is a random bytes message, cool right?').hex())
    print("number of bytes in a sha256 digest: ", len(sha256(b'')))

    ripemd160 = gen_ripemd160_with_variable_scope_protector_to_not_pollute_global_namespace()
    print(ripemd160(b'hello this is a test').hex())
    print("number of bytes in a RIPEMD-160 digest: ", len(ripemd160(b'')))
