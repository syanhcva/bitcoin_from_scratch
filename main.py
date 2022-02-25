from ecc import bitcoin_curve, bitcoin_gen, G, PublicKey

if __name__ == "__main__":
    secret_key = int.from_bytes(b'syanh is cooooooooooooooooooooooooooooooooooooooooooool :P', 'big') % bitcoin_curve.p
    assert 1 <= secret_key < bitcoin_gen.n
    print("secret key: {}".format(secret_key))
    public_key = secret_key * G
    print("public key: {}".format((public_key.x, public_key.y)))
    address = PublicKey.from_point(public_key).address(net='test', compressed=True)
    print("BTC address: {}".format(address))
    print()
    secret_key_2 = int.from_bytes(b'syanh is cooooooooooooooooooooooooooooooooooooooooool :P', 'big') % bitcoin_curve.p
    assert 1 <= secret_key_2 < bitcoin_gen.n
    print("secret key: {}".format(secret_key_2))
    public_key_2 = secret_key_2 * G
    print("public key: {}".format((public_key_2.x, public_key_2.y)))
    address_2 = PublicKey.from_point(public_key_2).address(net='test', compressed=True)
    print("BTC address: {}".format(address_2))