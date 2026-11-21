#!/usr/bin/env python3
"""
Independent exact-rational and arbitrary-precision numerical verification of
Conjecture 7.7 (Banić & Elezović, arXiv:2610.17046v1 / arXiv:2611.14735v1)
and the exact 2D-to-1D combinatorial reduction proved in Lean 4.

Usage:
    python scripts/verify_conjecture.py
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp


def h_adj_direct_exact(L: int) -> Fraction:
    """Direct exact rational evaluation of h_adj(L) from the 2D trinomial sum."""
    fact = [math.factorial(k) for k in range(L + 1)]
    L_fact = fact[L]
    total = 0
    for x1 in range(L + 1):
        f1 = fact[x1]
        for x2 in range(L - x1 + 1):
            x3 = L - x1 - x2
            coeff = L_fact // (f1 * fact[x2] * fact[x3])
            total += coeff * abs(x2 - x1) * abs(x3 - x2)
    return Fraction(total, 3**L)


def p3q_exact(q: int, x: int) -> Fraction:
    """Exact rational trinomial probability p_{3q}(x) = (3q)! / (3^{3q} x!^2 (3q-2x)!)."""
    if x < 0 or 2 * x > 3 * q:
        return Fraction(0)
    num = math.factorial(3 * q)
    den = (3 ** (3 * q)) * (math.factorial(x) ** 2) * math.factorial(3 * q - 2 * x)
    return Fraction(num, den)


def sums_abc_exact(q: int) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    """Exact rational values of p_{3q}(q), A(q), B(q), C(q)."""
    p0 = p3q_exact(q, q)
    numA = Fraction(0)
    numB = Fraction(0)
    numC = Fraction(0)
    for k in range(1, q + 1):
        pp = p3q_exact(q, q + k)
        pm = p3q_exact(q, q - k)
        diff = pp - pm
        summ = pp + pm
        ratio = Fraction(k, q)
        numA += diff
        numB += ratio * summ
        numC += (ratio**2) * diff
    return p0, numA / p0, numB / p0, numC / p0


def h_adj_1d_exact(L: int) -> Fraction:
    """Exact 1D reduction formulas hAdj_mod0, hAdj_mod1, hAdj_mod2."""
    assert L >= 3
    r = L % 3
    if r == 0:
        q = L // 3
        p0, A, B, _ = sums_abc_exact(q)
        return Fraction(3 * q, 9) + 2 * q * p0 * (1 + A - 2 * B) + 4 * (q**2) * p0
    elif r == 1:
        q = (L - 1) // 3
        p0, A, _, _ = sums_abc_exact(q)
        return (
            Fraction(3 * q + 1, 9)
            + Fraction(2 * (3 * q + 1), 3) * p0 * A
            + Fraction(2 * (6 * q + 1) * (3 * q + 1), 9) * p0
        )
    else:
        q = (L + 1) // 3
        p0, A, B, C = sums_abc_exact(q)
        return (
            Fraction(3 * q - 1, 9)
            + 2
            * q
            * p0
            * (
                (1 - Fraction(1, q)) * (1 + A)
                - (4 - Fraction(2, q)) * B
                + 4 * C
            )
            + 4 * (q**2) * p0
        )


def sums_abc_mp(q: int) -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    """
    Fast O(q) high-precision evaluation of p_{3q}(q), A(q), B(q), C(q)
    using exact consecutive recurrence ratios from the center x = q.
    """
    # p_{3q}(q) = (3q)! / (3^{3q} (q!)^3)
    log_p0 = mp.loggamma(3 * q + 1) - (3 * q) * mp.log(3) - 3 * mp.loggamma(q + 1)
    p0 = mp.exp(log_p0)

    # Right ratios: r_+(k) = p_{3q}(q+k) / p_{3q}(q), k = 0..floor(q/2)
    # r_+(k) / r_+(k-1) = (q - 2k + 2)(q - 2k + 1) / (q + k)^2
    # Left ratios: r_-(k) = p_{3q}(q-k) / p_{3q}(q), k = 0..q
    # r_-(k) / r_-(k-1) = (q - k + 1)^2 / ((q + 2k - 1)(q + 2k))
    rp = mp.mpf(1)
    rm = mp.mpf(1)
    A = mp.mpf(0)
    B = mp.mpf(0)
    C = mp.mpf(0)
    inv_q = mp.mpf(1) / q
    max_right = q // 2

    for k in range(1, q + 1):
        if k <= max_right:
            rp = rp * (q - 2 * k + 2) * (q - 2 * k + 1) / ((q + k) * (q + k))
        else:
            rp = mp.mpf(0)
        rm = rm * (q - k + 1) * (q - k + 1) / ((q + 2 * k - 1) * (q + 2 * k))
        u = k * inv_q
        diff = rp - rm
        summ = rp + rm
        A += diff
        B += u * summ
        C += (u * u) * diff
        # Early exit only if both tails are far below working precision
        if k > 20 and abs(rp) < mp.mpf("1e-85") and abs(rm) < mp.mpf("1e-85"):
            break

    return p0, A, B, C


def h_adj_1d_mp(q: int, r: int) -> mp.mpf:
    """
    High-precision h_adj(L) for:
      r = 0 -> L = 3q
      r = 1 -> L = 3q + 1
      r = 2 -> L = 3q - 1
    """
    p0, A, B, C = sums_abc_mp(q)
    qf = mp.mpf(q)
    if r == 0:
        return (3 * qf) / 9 + 2 * qf * p0 * (1 + A - 2 * B) + 4 * qf * qf * p0
    elif r == 1:
        return (
            (3 * qf + 1) / 9
            + (2 * (3 * qf + 1) / 3) * p0 * A
            + (2 * (6 * qf + 1) * (3 * qf + 1) / 9) * p0
        )
    elif r == 2:
        return (
            (3 * qf - 1) / 9
            + 2 * qf * p0 * ((1 - 1 / qf) * (1 + A) - (4 - 2 / qf) * B + 4 * C)
            + 4 * qf * qf * p0
        )
    else:
        raise ValueError("r must be 0, 1, or 2")


def richardson_extrapolate(xs: list[mp.mpf], ys: list[mp.mpf]) -> mp.mpf:
    """Neville-Richardson extrapolation to h = 1/x -> 0."""
    n = len(xs)
    hs = [mp.mpf(1) / x for x in xs]
    table = list(ys)
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            table[i] = (hs[i - j] * table[i] - hs[i] * table[i - 1]) / (
                hs[i - j] - hs[i]
            )
    return table[-1]


def main() -> None:
    mp.mp.dps = 80

    print("=== 1. Exact Rational Verification of 2D-to-1D Identities (L = 3..45) ===")
    for L in range(3, 46):
        direct = h_adj_direct_exact(L)
        reduced = h_adj_1d_exact(L)
        assert direct == reduced, f"Mismatch at L={L}: {direct} != {reduced}"
    print("PASS: Exact rational equality verified for all 43 values L = 3..45 (0/1 error).")

    # Exact closed-form constants from Theorem 1.1 (Conjecture 7.7)
    sqrt3 = mp.sqrt(3)
    pi = mp.pi
    cL = 2 * sqrt3 / (3 * pi) + mp.mpf(1) / 9
    aStar = -2 * sqrt3 / (9 * pi)
    b0_exact = 32 * sqrt3 / (81 * pi)
    b1_exact = -22 * sqrt3 / (81 * pi)
    b2_exact = -22 * sqrt3 / (81 * pi)
    d0_exact = -4 * sqrt3 / (81 * pi)
    aTri_exact = mp.mpf(1) / 32 - 4 * sqrt3 / 243
    gamma2_exact = -mp.mpf(1) / (32 * pi) - 8 * sqrt3 / (243 * pi)
    C1 = mp.mpf(10) / 3 + (8 * sqrt3 - 20) / pi
    beta1 = (8 * sqrt3 - 9) / (18 * pi)
    K0 = C1 / beta1
    C12_exact = 2 * gamma2_exact * (K0 ** mp.mpf("1.5")) / beta1

    print("\n=== 2. Exact Closed-Form Constants (50 digits) ===")
    print(f"b_0        = {mp.nstr(b0_exact, 45)}")
    print(f"b_1 = b_2  = {mp.nstr(b1_exact, 45)}")
    print(f"d_0        = {mp.nstr(d0_exact, 45)}")
    print(f"a_triangle = {mp.nstr(aTri_exact, 45)}")
    print(f"gamma_2    = {mp.nstr(gamma2_exact, 45)}")
    print(f"K_0        = {mp.nstr(K0, 30)}")
    print(f"C_(1/2)    = {mp.nstr(C12_exact, 30)}")

    print("\n=== 3. Convergence of 1D Normalized Sums A(q), B(q), C(q) ===")
    q_grid = [10, 30, 100, 300, 1000, 3000]
    abc_rows = []
    for q in q_grid:
        p0, A, B, C = sums_abc_mp(q)
        eA = q * (A - (-mp.mpf(1) / 9 - mp.mpf(4) / (243 * q)))
        eB = q * (B - (mp.mpf(1) / 3 - mp.mpf(2) / (27 * q)))
        eC = q * (C - (-mp.mpf(2) / (27 * q)))
        abc_rows.append(
            {
                "q": q,
                "A": float(A),
                "B": float(B),
                "C": float(C),
                "eA": float(eA),
                "eB": float(eB),
                "eC": float(eC),
            }
        )
        print(
            f"q={q:4d} | q*err_A={mp.nstr(eA, 8):>14s} | "
            f"q*err_B={mp.nstr(eB, 8):>14s} | q*err_C={mp.nstr(eC, 8):>14s}"
        )

    print("\n=== 4. Convergence of Residue Classes L*(h_adj(L) - c_L*L - a_*) ===")
    res_rows = []
    for q in q_grid:
        L0, L1, L2 = 3 * q, 3 * q + 1, 3 * q - 1
        val0 = L0 * (h_adj_1d_mp(q, 0) - cL * L0 - aStar)
        val1 = L1 * (h_adj_1d_mp(q, 1) - cL * L1 - aStar)
        val2 = L2 * (h_adj_1d_mp(q, 2) - cL * L2 - aStar)
        err0 = val0 - b0_exact
        err1 = val1 - b1_exact
        err2 = val2 - b2_exact
        res_rows.append(
            {
                "q": q,
                "L0": L0,
                "b0_approx": mp.nstr(val0, 15),
                "err0": float(err0),
                "b1_approx": mp.nstr(val1, 15),
                "err1": float(err1),
                "b2_approx": mp.nstr(val2, 15),
                "err2": float(err2),
            }
        )
        print(
            f"q={q:4d} | err(r=0)={mp.nstr(err0, 6):>12s} | "
            f"err(r=1)={mp.nstr(err1, 6):>12s} | err(r=2)={mp.nstr(err2, 6):>12s}"
        )

    print("\n=== 5. High-Order Richardson Extrapolation (40+ digit cross-check) ===")
    q_rich = [200 + 80 * i for i in range(28)]  # q = 200..2360 (L up to 7081)
    xs0 = [mp.mpf(3 * q) for q in q_rich]
    xs1 = [mp.mpf(3 * q + 1) for q in q_rich]
    xs2 = [mp.mpf(3 * q - 1) for q in q_rich]
    ys0 = [L * (h_adj_1d_mp(q, 0) - cL * L - aStar) for q, L in zip(q_rich, xs0)]
    ys1 = [L * (h_adj_1d_mp(q, 1) - cL * L - aStar) for q, L in zip(q_rich, xs1)]
    ys2 = [L * (h_adj_1d_mp(q, 2) - cL * L - aStar) for q, L in zip(q_rich, xs2)]

    b0_r = richardson_extrapolate(xs0, ys0)
    b1_r = richardson_extrapolate(xs1, ys1)
    b2_r = richardson_extrapolate(xs2, ys2)
    d0_r = (b0_r + b1_r + b2_r) / 3
    aTri_r = mp.mpf(1) / 32 + pi / 9 * (b0_r + b1_r + b2_r)
    gamma2_r = (64 * aTri_r - 3) / (32 * pi)

    errs = {
        "b0_abs_err": float(abs(b0_r - b0_exact)),
        "b1_abs_err": float(abs(b1_r - b1_exact)),
        "b2_abs_err": float(abs(b2_r - b2_exact)),
        "d0_abs_err": float(abs(d0_r - d0_exact)),
        "aTriangle_abs_err": float(abs(aTri_r - aTri_exact)),
        "gamma2_abs_err": float(abs(gamma2_r - gamma2_exact)),
    }
    for k, v in errs.items():
        print(f"  {k:20s} = {v:.3e}")
        assert v < 1e-40, f"Richardson error too large for {k}: {v}"
    print("PASS: All 6 constants match closed forms to > 40 decimal digits!")

    out_path = Path(__file__).parent / "verification_results.json"
    out_data = {
        "exact_rational_checked_L": [3, 45],
        "constants_50dps": {
            "cL": mp.nstr(cL, 50),
            "aStar": mp.nstr(aStar, 50),
            "b0": mp.nstr(b0_exact, 50),
            "b1": mp.nstr(b1_exact, 50),
            "b2": mp.nstr(b2_exact, 50),
            "d0": mp.nstr(d0_exact, 50),
            "aTriangle": mp.nstr(aTri_exact, 50),
            "gamma2": mp.nstr(gamma2_exact, 50),
            "K0": mp.nstr(K0, 40),
            "C12": mp.nstr(C12_exact, 40),
        },
        "abc_convergence": abc_rows,
        "residue_convergence": res_rows,
        "richardson_errors": errs,
    }
    out_path.write_text(json.dumps(out_data, indent=2), encoding="utf-8")
    print(f"\nWrote verification summary to {out_path}")


if __name__ == "__main__":
    main()
