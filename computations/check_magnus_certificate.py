#!/usr/bin/env python3
"""Independent verifier for the class-2 pair-count parity certificate.

Builds the 54 integer equations E', VV, PW, WW from scratch, applies the
explicit integer linear combination displayed in the accompanying paper,
and checks that the combined left-hand
side is identically 8*(R12 + Q13 - Q23 - Q31 + Q32 - S31 + S32) while the
combined right-hand side is 4*w.  Prints PASS/FAIL.
"""

G = list(range(4))
NZ = [1, 2, 3]

Pv = {(i, g): f"P{i}{g}" for i in NZ for g in G}
Qv = {(g, j): f"Q{g}{j}" for g in G for j in NZ}
Sv = {(g, h): f"S{g}{h}" for g in G for h in G if g != h}
Rv = {(i, j): f"R{i}{j}" for i in NZ for j in NZ if i != j}

varnames = (
    list(Rv.values()) + list(Pv.values()) + list(Qv.values()) + list(Sv.values())
)
idx = {name: k for k, name in enumerate(varnames)}

eqs = []  # (coeff dict var -> int, rhs dict {'w': int})


def add(coeff, rhs):
    eqs.append((coeff, rhs))


# E'_ijc : P_{i,j+c} + Q_{i+c,j} + S_{i+c,j+c} + R_ij = 0
for i in NZ:
    for j in NZ:
        if i == j:
            continue
        for c in G:
            add(
                {
                    Pv[(i, j ^ c)]: 1,
                    Qv[(i ^ c, j)]: 1,
                    Sv[(i ^ c, j ^ c)]: 1,
                    Rv[(i, j)]: 1,
                },
                {"w": 0},
            )
# VV_ij : R_ij + R_ji = w
for i in NZ:
    for j in NZ:
        if i == j:
            continue
        add({Rv[(i, j)]: 1, Rv[(j, i)]: 1}, {"w": 1})
# PW_ig : P_ig + Q_gi = -w
for i in NZ:
    for g in G:
        add({Pv[(i, g)]: 1, Qv[(g, i)]: 1}, {"w": -1})
# WW_gh : S_gh + S_hg = w
for g in G:
    for h in G:
        if g == h:
            continue
        add({Sv[(g, h)]: 1, Sv[(h, g)]: 1}, {"w": 1})

N = len(eqs)
pairs = [(i, j) for i in NZ for j in NZ if i != j]
pairs2 = [(g, h) for g in G for h in G if g != h]

cert = {}


def addE(i, j, c, coef):
    cert[4 * pairs.index((i, j)) + c] = coef


def addVV(i, j, coef):
    cert[24 + pairs.index((i, j))] = coef


def addPW(i, g, coef):
    cert[30 + 4 * (i - 1) + g] = coef


def addWW(g, h, coef):
    cert[42 + pairs2.index((g, h))] = coef


# ---- the certificate table ----
addE(1, 2, 0, 5)
addE(1, 2, 1, -3)
addE(1, 2, 2, 5)
addE(1, 2, 3, -3)
addE(1, 3, 0, 3)
addE(1, 3, 1, 3)
addE(1, 3, 2, -5)
addE(1, 3, 3, -5)
addE(2, 1, 0, 3)
addE(2, 1, 1, -5)
addE(2, 1, 2, 3)
addE(2, 1, 3, -5)
addE(2, 3, 0, -3)
addE(2, 3, 1, 5)
addE(2, 3, 2, -3)
addE(2, 3, 3, 5)
addE(3, 1, 0, -3)
addE(3, 1, 1, 5)
addE(3, 1, 2, -3)
addE(3, 1, 3, -3)
addE(3, 2, 0, 3)
addE(3, 2, 1, 3)
addE(3, 2, 2, -5)
addE(3, 2, 3, 3)
addVV(1, 2, 4)
addVV(1, 3, 4)
addVV(2, 3, -4)
addPW(1, 1, 8)
addPW(1, 2, -8)

# ---- combine ----
form = {}
rhs = 0
for e, coef in cert.items():
    coeff, r = eqs[e]
    for var, c in coeff.items():
        form[var] = form.get(var, 0) + coef * c
    rhs += coef * r["w"]

expected = {
    Rv[(1, 2)]: 8,
    Qv[(1, 3)]: 8,
    Qv[(2, 3)]: -8,
    Qv[(3, 1)]: -8,
    Qv[(3, 2)]: 8,
    Sv[(3, 1)]: -8,
    Sv[(3, 2)]: 8,
}

ok = True
for var in varnames:
    if form.get(var, 0) != expected.get(var, 0):
        ok = False
        print("MISMATCH", var, form.get(var, 0), expected.get(var, 0))
print("RHS (w-coefficient):", rhs)
print("form matches expected:", ok)
if ok and rhs == 4:
    print(
        "PASS: 8*(R12+Q13-Q23-Q31+Q32-S31+S32) = 4w, "
        "so w = 2*(R12+Q13-Q23-Q31+Q32-S31+S32) is even."
    )
else:
    raise SystemExit("FAIL")
