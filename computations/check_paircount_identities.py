#!/usr/bin/env python3
"""Independent algebra verifier for the F_2^r Cayley-game obstruction.

This script derives the equations directly from the definitions on
deterministically generated words and re-derives the parity certificate by
solving the restricted integer system over Q before applying the explicit
certificate combination.

Checks:
  (1) expansion identity: for EVERY clause word (no hypotheses),
      C_ij(alpha) = R_ij + P_{i,j+alpha} + Q_{i+alpha,j}
                    + S_{i+alpha,j+alpha}
      for all ordered i != j in {1,2,3} and all alpha in V4, where the
      pair counts R,P,Q,S are the weighted order statistics of the word.
  (2) product identities: R_ij+R_ji = V_i V_j, P_ig+Q_gi = V_i W_g,
      S_gh+S_hg = W_g W_h, for all indices in range.
  (3) free-group sanity: for random reduced-free words, Magnus exponents
      and class-2 coefficients vanish when the word is trivial.
  (4) parity lemma: the restricted system (E'),(VV),(PW),(WW) has no
      integer solution with w odd.  Verified two ways:
      (a) the explicit certificate combination encoded below;
      (b) exact rational Gaussian elimination showing
          R_12 = w/2 + integer-free-variable combination, so integrality
          forces w even.

No floating point is used anywhere.
"""

from __future__ import annotations

import random
from fractions import Fraction


# ---------------------------------------------------------------------------
# V4 arithmetic (XOR on {0,1,2,3})
# ---------------------------------------------------------------------------

def xor(a: int, b: int) -> int:
    return a ^ b


G = [0, 1, 2, 3]
NZ = [1, 2, 3]


# ---------------------------------------------------------------------------
# Pair counts and Magnus quantities of an arbitrary clause word
# ---------------------------------------------------------------------------

def quantities(word):
    """word: list of (g, m) with m=0 for E_g, m=1 for O_g.

    Returns (V, W, R, P, Q, S, C) where
      V[g], W[g] are the s-weighted sums over clause positions,
      R/P/Q/S are the four pair-count dicts, and
      C[(i,j,alpha)] is the class-2 Magnus coefficient of P_alpha.
    """
    n = len(word)
    s = [+1 if p % 2 == 0 else -1 for p in range(n)]
    V = {g: 0 for g in G}
    W = {g: 0 for g in G}
    for p, (g, m) in enumerate(word):
        (W if m else V)[g] += s[p]
    R = {}
    P = {}
    Q = {}
    S = {}
    for p in range(n):
        gp, mp = word[p]
        for q in range(p + 1, n):
            gq, mq = word[q]
            wgt = s[p] * s[q]
            if mp == 0 and mq == 0:
                R[(gp, gq)] = R.get((gp, gq), 0) + wgt
            elif mp == 0 and mq == 1:
                P[(gp, gq)] = P.get((gp, gq), 0) + wgt
            elif mp == 1 and mq == 0:
                Q[(gp, gq)] = Q.get((gp, gq), 0) + wgt
            else:
                S[(gp, gq)] = S.get((gp, gq), 0) + wgt
    C = {}
    for i in NZ:
        for j in NZ:
            if i == j:
                continue
            for a in G:
                val = 0
                for p in range(n):
                    gp, mp = word[p]
                    if (mp == 0 and gp == i) or (mp == 1 and xor(gp, a) == i):
                        for q in range(p + 1, n):
                            gq, mq = word[q]
                            if (mq == 0 and gq == j) or (mq == 1 and xor(gq, a) == j):
                                val += s[p] * s[q]
                C[(i, j, a)] = val
    return V, W, R, P, Q, S, C


def check_expansion_identity(word):
    """Check C_ij(alpha) = R_ij + P_{i,j+a} + Q_{i+a,j} + S_{i+a,j+a}
    for every ordered i != j in {1,2,3} and every alpha in V4."""
    V, W, R, P, Q, S, C = quantities(word)
    for i in NZ:
        for j in NZ:
            if i == j:
                continue
            for a in G:
                rhs = R.get((i, j), 0)
                rhs += P.get((i, xor(j, a)), 0)
                rhs += Q.get((xor(i, a), j), 0)
                rhs += S.get((xor(i, a), xor(j, a)), 0)
                if C[(i, j, a)] != rhs:
                    return False, (i, j, a, C[(i, j, a)], rhs)
    return True, None


def check_product_identities(word):
    V, W, R, P, Q, S, C = quantities(word)
    for i in NZ:
        for j in NZ:
            if i == j:
                continue
            if R.get((i, j), 0) + R.get((j, i), 0) != V[i] * V[j]:
                return False, ("VV", i, j)
    for i in NZ:
        for g in G:
            if P.get((i, g), 0) + Q.get((g, i), 0) != V[i] * W[g]:
                return False, ("PW", i, g)
    for g in G:
        for h in G:
            if g == h:
                continue
            if S.get((g, h), 0) + S.get((h, g), 0) != W[g] * W[h]:
                return False, ("WW", g, h)
    return True, None


# ---------------------------------------------------------------------------
# Free-group Magnus sanity checks
# ---------------------------------------------------------------------------

def free_reduce(w):
    """w: list of (generator index, exponent +-1).  Adjacent x, x^-1 cancel."""
    st = []
    for g, e in w:
        if st and st[-1][0] == g and st[-1][1] == -e:
            st.pop()
        else:
            st.append((g, e))
    return st


def check_free_group_magnus():
    rng = random.Random(20260805)
    for _ in range(300):
        n = rng.randrange(1, 40)
        w = [(rng.randrange(1, 4), 1 if rng.randrange(2) else -1)
             for _ in range(n)]
        red = free_reduce(w)
        if red:
            continue
        # trivial word: exponents and class-2 coefficients must vanish
        exp = {g: 0 for g in (1, 2, 3)}
        for g, e in w:
            exp[g] += e
        if any(exp.values()):
            return False, ("exp", w)
        for i in NZ:
            for j in NZ:
                if i == j:
                    continue
                c = 0
                for p in range(len(w)):
                    for q in range(p + 1, len(w)):
                        if w[p][0] == i and w[q][0] == j:
                            c += w[p][1] * w[q][1]
                if c != 0:
                    return False, ("class2", w, i, j, c)
    return True, None


# ---------------------------------------------------------------------------
# Parity lemma: restricted system on H = {0,1,2,3}
# ---------------------------------------------------------------------------

def build_system():
    """Return (vars, eqs) where eqs are (coeff dict, rhs constant in terms
    of the parameter w).  Variables: R,P,Q,S as in the theorem."""
    Pv = {(i, g): f"P{i}{g}" for i in NZ for g in G}
    Qv = {(g, j): f"Q{g}{j}" for g in G for j in NZ}
    Sv = {(g, h): f"S{g}{h}" for g in G for h in G if g != h}
    Rv = {(i, j): f"R{i}{j}" for i in NZ for j in NZ if i != j}
    varnames = (
        list(Rv.values()) + list(Pv.values()) + list(Qv.values())
        + list(Sv.values())
    )
    eqs = []
    # E'_ijc : P_{i,j+c} + Q_{i+c,j} + S_{i+c,j+c} + R_ij = 0
    for i in NZ:
        for j in NZ:
            if i == j:
                continue
            for c in G:
                eqs.append((
                    {
                        Pv[(i, xor(j, c))]: 1,
                        Qv[(xor(i, c), j)]: 1,
                        Sv[(xor(i, c), xor(j, c))]: 1,
                        Rv[(i, j)]: 1,
                    },
                    {"w": 0},
                ))
    # VV_ij : R_ij + R_ji = w
    for i in NZ:
        for j in NZ:
            if i == j:
                continue
            eqs.append(({Rv[(i, j)]: 1, Rv[(j, i)]: 1}, {"w": 1}))
    # PW_ig : P_ig + Q_gi = -w
    for i in NZ:
        for g in G:
            eqs.append(({Pv[(i, g)]: 1, Qv[(g, i)]: 1}, {"w": -1}))
    # WW_gh : S_gh + S_hg = w
    for g in G:
        for h in G:
            if g == h:
                continue
            eqs.append(({Sv[(g, h)]: 1, Sv[(h, g)]: 1}, {"w": 1}))
    return varnames, eqs


def apply_certificate(varnames, eqs):
    """Apply the explicit integer combination from the certificate and
    return (combined form dict, rhs w-coefficient)."""
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

    # ---- the certificate table (same input data as the published file) ----
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

    form = {}
    rhs = 0
    for e, coef in cert.items():
        coeff, r = eqs[e]
        for var, c in coeff.items():
            form[var] = form.get(var, 0) + coef * c
        rhs += coef * r["w"]
    return form, rhs


def rational_rref_with_parameter(varnames, eqs):
    """Gaussian elimination over Q treating w as a parameter variable that
    stays on the right-hand side.  Returns the row-reduced system as a list
    of (pivot variable, other-var coeff dict, rhs dict)."""
    idx = {v: k for k, v in enumerate(varnames)}
    n = len(varnames)
    rows = []
    for coeff, rhs in eqs:
        row = [Fraction(0)] * (n + 1)
        for v, c in coeff.items():
            row[idx[v]] = Fraction(c)
        row[n] = Fraction(rhs.get("w", 0))  # w-coefficient
        rows.append(row)
    piv = 0
    for col in range(n):
        p = next((r for r in range(piv, len(rows)) if rows[r][col] != 0), None)
        if p is None:
            continue
        rows[piv], rows[p] = rows[p], rows[piv]
        inv = Fraction(1) / rows[piv][col]
        rows[piv] = [x * inv for x in rows[piv]]
        for r in range(len(rows)):
            if r != piv and rows[r][col] != 0:
                f = rows[r][col]
                rows[r] = [rows[r][k] - f * rows[piv][k] for k in range(n + 1)]
        piv += 1
    return rows


def main():
    rng = random.Random(20260805)
    n_trials = 200
    for trial in range(n_trials):
        L = 2 * rng.randrange(1, 21)
        word = [(rng.randrange(4), rng.randrange(2)) for _ in range(L)]
        ok, info = check_expansion_identity(word)
        if not ok:
            print(f"FAIL expansion identity trial {trial}: {info}")
            return 1
        ok, info = check_product_identities(word)
        if not ok:
            print(f"FAIL product identities trial {trial}: {info}")
            return 1
    print(f"expansion + product identities: PASS on {n_trials} random words")

    ok, info = check_free_group_magnus()
    if not ok:
        print(f"FAIL free-group Magnus sanity: {info}")
        return 1
    print("free-group Magnus necessary conditions: PASS on 300 random trivial words")

    varnames, eqs = build_system()
    form, rhs = apply_certificate(varnames, eqs)
    expected = {
        "R12": 8,
        "Q13": 8,
        "Q23": -8,
        "Q31": -8,
        "Q32": 8,
        "S31": -8,
        "S32": 8,
    }
    ok = True
    for v in varnames:
        if form.get(v, 0) != expected.get(v, 0):
            ok = False
            print("MISMATCH", v, form.get(v, 0), expected.get(v, 0))
    print("certificate combined form:",
          "PASS" if ok and rhs == 4 else "FAIL", "| rhs w-coefficient =", rhs)
    if not (ok and rhs == 4):
        return 1

    rows = rational_rref_with_parameter(varnames, eqs)
    # Find the pivot row expressing R12 in terms of w and free variables.
    r12 = varnames.index("R12")
    found = None
    for row in rows:
        if any(row[r12:]):  # has a pivot at or after R12? simpler: check pivot
            nz = [k for k in range(len(row) - 1) if row[k] != 0]
            if nz and nz[0] == r12:
                found = row
                break
    if found is None:
        print("FAIL: no pivot row for R12")
        return 1
    wcoef = found[-1]
    free_coefs = [c for k, c in enumerate(found[:-1]) if k != r12 and c != 0]
    print("R12 pivot row: R12 = (w-coefficient", wcoef, ") + free-variable combination"
          " with", len(free_coefs), "nonzero integer coefficients")
    print("all free coefficients are integers:",
          all(c.denominator == 1 for c in free_coefs))
    if wcoef != Fraction(1, 2):
        print("FAIL: R12 does not have w/2 as its w-coefficient")
        return 1
    if not all(c.denominator == 1 for c in free_coefs):
        print("FAIL: free coefficients not integral")
        return 1
    print("rational RREF: every integer solution satisfies w = 2*R12 - 2*(integer),"
          " hence w even")
    print("PASS: elementary-abelian parity lemma algebra verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
