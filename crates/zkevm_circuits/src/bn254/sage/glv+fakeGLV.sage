def phi0(E, P):
    """
    j=0 endomorphism
    :param E: Elliptic curve
    :param P: point on E
    :return: point lam*P
    """
    return E(P[0]*w, P[1])


# BN254 Base field:
p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
Fp = GF(p)

# BN254 scalar field
r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
Fr = GF(r)

print(Integer(r).nbits())
print(254 >> 2) # 63
print(63 + 9) # 72

# BN254 (alt_bn128) is defined by y^2 = x^3 + 3:
E = EllipticCurve(Fp, [0, 3])

# Define the generator:
G = E(1,2)

Px = Fp(19866297484586973404676118505819988588375821317410189276075924520646304140243)
Py = Fp(17716871188953548858735042529475562105487934609630310157213829999115059870465)
P = E(Px, Py)

s = Fr(21391913909508507526530231977791181262274630332094910859362747544589655449059)

l = Fr(4407920970296243842393367215006156084916469457145843978461)
w = Fp(2203960485148121921418603742825762020974279258880205651966)

Q = s * P

s0 = Fr(75623561034882502558272301667177083182)
s1 = Fr(80419626531725512023491232008924591071)
s0_was_negated = False
s1_was_negated = True

assert((s0 - s1*l) == s)

u0 = Fr(0x000000000000000000000000000000000000000000000000a083bab79119aae3)
u1 = Fr(0x0000000000000000000000000000000000000000000000007e0e78d940e4296f)
v0 = Fr(0x00000000000000000000000000000000000000000000000046fb0e7e514e5ea0)
v1 = Fr(0x0000000000000000000000000000000000000000000000008534399c6f17bc3c)

print("u0.nbits() = ", Integer(u0).nbits())
print("u1.nbits() = ", Integer(u1).nbits())
print("v0.nbits() = ", Integer(v0).nbits())
print("v1.nbits() = ", Integer(v1).nbits())

# s(v0 + λ*v1) - u0 + λ*u1 = 0
assert(s * (v0 + l*v1) - (u0 + l*u1) == 0)

assert(s*P - Q == E(0))

assert((s0-l*s1)*P - Q == E(0))

assert((v0+l*v1)*(s0-l*s1)*P - (v0+l*v1)*Q == E(0))

assert((u0+l*u1)*P - (v0+l*v1)*Q == E(0))

assert(u0*P + u1*phi0(E, P) - v0*Q - v1*phi0(E, Q) == E(0))

table = [
    # +P + Q + φ(P) + φ(Q)
    P + Q + phi0(E, P) + phi0(E, Q),
    # +P + Q + φ(P) - φ(Q)
    P + Q + phi0(E, P) - phi0(E, Q),
    # +P + Q - φ(P) + φ(Q)
    P + Q - phi0(E, P) + phi0(E, Q),
    # +P + Q - φ(P) - φ(Q)
    P + Q - phi0(E, P) - phi0(E, Q),
    # +P - Q + φ(P) + φ(Q)
    P - Q + phi0(E, P) + phi0(E, Q),
    # +P - Q + φ(P) - φ(Q)
    P - Q + phi0(E, P) - phi0(E, Q),
    # +P - Q - φ(P) + φ(Q)
    P - Q - phi0(E, P) + phi0(E, Q),
    # +P - Q - φ(P) - φ(Q)
    P - Q - phi0(E, P) - phi0(E, Q),
    # -P + Q + φ(P) + φ(Q)
    -P + Q + phi0(E, P) + phi0(E, Q),
    # -P + Q + φ(P) - φ(Q)
    -P + Q + phi0(E, P) - phi0(E, Q),
    # -P + Q - φ(P) + φ(Q)
    -P + Q - phi0(E, P) + phi0(E, Q),
    # -P + Q - φ(P) - φ(Q)
    -P + Q - phi0(E, P) - phi0(E, Q),
    # -P - Q + φ(P) + φ(Q)
    -P - Q + phi0(E, P) + phi0(E, Q),
    # -P - Q + φ(P) - φ(Q)
    -P - Q + phi0(E, P) - phi0(E, Q),
    # -P - Q - φ(P) + φ(Q)
    -P - Q - phi0(E, P) + phi0(E, Q),
    # -P - Q - φ(P) - φ(Q)
    -P - Q - phi0(E, P) - phi0(E, Q)
]

for i in range(16):
    print(f"COMBINATION NUMBER: {i}")
    x, y = table[i].xy()
    print(f"x = {hex(x)}")
    print(f"y = {hex(y)}")
