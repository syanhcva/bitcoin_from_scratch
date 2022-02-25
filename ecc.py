from __future__ import annotations # PEP 563: Postponed Evaluation of Annotations
from dataclasses import dataclass # https://docs.python.org/3/library/dataclasses.html I like these a lot
from hash_func import gen_sha256_with_variable_scope_protector_to_not_pollute_global_namespace
sha256 = gen_sha256_with_variable_scope_protector_to_not_pollute_global_namespace()
from hash_func import gen_ripemd160_with_variable_scope_protector_to_not_pollute_global_namespace
ripemd160 = gen_ripemd160_with_variable_scope_protector_to_not_pollute_global_namespace()
@dataclass
class Curve:
    """
    Elliptic Curve over the field of integers modulo a prime.
    Points on the curve satisfy y^2 = x^3 + a*x + b (mod p).
    """
    p: int # the prime modulus of the finite field
    a: int
    b: int

@dataclass()
class Point:
    """ An integer point (x,y) on a Curve """
    curve: Curve
    x: int
    y: int

@dataclass
class Generator:
    """
    A generator over a curve: an initial point and the (pre-computed) order
    """
    G: Point     # a generator point on the curve
    n: int       # the order of the generating point, so 0*G = n*G = INF

# secp256k1 uses a = 0, b = 7, so we're dealing with the curve y^2 = x^3 + 7 (mod p)
bitcoin_curve = Curve(
    p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
    a = 0x0000000000000000000000000000000000000000000000000000000000000000, # a = 0
    b = 0x0000000000000000000000000000000000000000000000000000000000000007, # b = 7
)

G = Point(
    bitcoin_curve,
    x = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    y = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8,
)

bitcoin_gen = Generator(
    G = G,
    # the order of G is known and can be mathematically derived
    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
)


INF = Point(None, None, None) # special point at "infinity", kind of like a zero

def extended_euclidean_algorithm(a, b):
    """
    Returns (gcd, x, y) s.t. a * x + b * y == gcd
    This function implements the extended Euclidean
    algorithm and runs in O(log b) in the worst case,
    taken from Wikipedia.
    """
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    return old_r, old_s, old_t

def inv(n, p):
    """ returns modular multiplicate inverse m s.t. (n * m) % p == 1 """
    gcd, x, y = extended_euclidean_algorithm(n, p) # pylint: disable=unused-variable
    return x % p

def elliptic_curve_addition(self, other: Point) -> Point:
    # handle special case of P + 0 = 0 + P = 0
    if self == INF:
        return other
    if other == INF:
        return self
    # handle special case of P + (-P) = 0
    if self.x == other.x and self.y != other.y:
        return INF
    # compute the "slope"
    if self.x == other.x: # (self.y = other.y is guaranteed too per above check)
        m = (3 * self.x**2 + self.curve.a) * inv(2 * self.y, self.curve.p)
    else:
        m = (self.y - other.y) * inv(self.x - other.x, self.curve.p)
    # compute the new point
    rx = (m**2 - self.x - other.x) % self.curve.p
    ry = (-(m*(rx - self.x) + self.y)) % self.curve.p
    return Point(self.curve, rx, ry)

Point.__add__ = elliptic_curve_addition


def double_and_add(self, k: int) -> Point:
    assert isinstance(k, int) and k >= 0
    result = INF
    append = self
    while k:
        if k & 1:
            result += append
        append += append
        k >>= 1
    return result

# monkey patch double and add into the Point class for convenience
Point.__rmul__ = double_and_add

def check_on_curve(x, y):
    return (y**2 - x**3 - 7)%bitcoin_curve.p ==0

alphabet = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'

def b58encode(b: bytes) -> str:
    assert len(b) == 25 # version is 1 byte, pkb_hash 20 bytes, checksum 4 bytes
    n = int.from_bytes(b, 'big')
    chars = []
    while n:
        n, i = divmod(n, 58)
        chars.append(alphabet[i])
    # special case handle the leading 0 bytes... ¯\_(ツ)_/¯
    num_leading_zeros = len(b) - len(b.lstrip(b'\x00'))
    res = num_leading_zeros * alphabet[0] + ''.join(reversed(chars))
    return res

class PublicKey(Point):
    """
    The public key is just a Point on a Curve, but has some additional specific
    encoding / decoding functionality that this class implements.
    """

    @classmethod
    def from_point(cls, pt: Point):
        """ promote a Point to be a PublicKey """
        return cls(pt.curve, pt.x, pt.y)

    def encode(self, compressed, hash160=False):
        """ return the SEC bytes encoding of the public key Point """
        # calculate the bytes
        if compressed:
            # (x,y) is very redundant. Because y^2 = x^3 + 7,
            # we can just encode x, and then y = +/- sqrt(x^3 + 7),
            # so we need one more bit to encode whether it was the + or the -
            # but because this is modular arithmetic there is no +/-, instead
            # it can be shown that one y will always be even and the other odd.
            prefix = b'\x02' if self.y % 2 == 0 else b'\x03'
            pkb = prefix + self.x.to_bytes(32, 'big')
        else:
            pkb = b'\x04' + self.x.to_bytes(32, 'big') + self.y.to_bytes(32, 'big')
        # hash if desired
        return ripemd160(sha256(pkb)) if hash160 else pkb

    def address(self, net: str, compressed: bool) -> str:
        """ return the associated bitcoin address for this public key as string """
        # encode the public key into bytes and hash to get the payload
        pkb_hash = self.encode(compressed=compressed, hash160=True)
        # add version byte (0x00 for Main Network, or 0x6f for Test Network)
        version = {'main': b'\x00', 'test': b'\x6f'}
        ver_pkb_hash = version[net] + pkb_hash
        # calculate the checksum
        checksum = sha256(sha256(ver_pkb_hash))[:4]
        # append to form the full 25-byte binary Bitcoin Address
        byte_address = ver_pkb_hash + checksum
        # finally b58 encode the result
        b58check_address = b58encode(byte_address)
        return b58check_address


if __name__ == "__main__":
    print(bitcoin_curve)
    print(G)
    on_curve = (G.y**2 - G.x**3 - 7) % bitcoin_curve.p == 0
    print("generator is on the curve: {}\n".format(on_curve))

    import random
    x = random.randrange(0, bitcoin_curve.p)
    y = random.randrange(0, bitcoin_curve.p)
    on_curve = (y**2 - x**3 - 7)%bitcoin_curve.p == 0
    print("random point (x,y) = ({},{}) on curve: {}\n".format(x,y, on_curve))

    print("TESTING ADDITION AND MULTIPLICATION ON ECC")
    sk = 2
    pk = G+G
    pk_m = 2*G
    print("secret key: {}, public key: {}".format(sk, (pk.x, pk.y)))
    print("public key is on curve: {}".format(check_on_curve(pk.x, pk.y)))
    print("multiplication and addition produce the same result: {}".format(pk == pk_m))

    sk = 4
    pk = G+G+G+G
    pk_m = 4*G
    print("secret key: {}, public key: {}".format(sk, (pk.x, pk.y)))
    print("public key is on curve: {}".format(check_on_curve(pk.x, pk.y)))
    print("multiplication and addition produce the same result: {}".format(pk == pk_m))
    print()

    secret_key = int.from_bytes(b'syanh is cooooooooooooooooooooooooooooooooooooooooooool :P', 'big') % bitcoin_curve.p  # this is how I will do it for reproducibility
    # secret_key = random.randrange(0, bitcoin_curve.p)
    assert 1 <= secret_key < bitcoin_gen.n
    print("secret key: {}".format(secret_key))
    public_key = secret_key*G
    print("public key: {}".format((public_key.x, public_key.y)))
    print("public key is on curve: {}".format(check_on_curve(public_key.x, public_key.y)))
    address = PublicKey.from_point(public_key).address(net='test', compressed=True)
    print(address)