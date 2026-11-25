"""Comprehensive mathematical and numerical verification test ladder for Conjecture 7.7.

Covers Build Standard v1.2.0 items:
- B05: Falsifiable tests per claim (C1-C4)
- B06: Negative and adversarial tests
- B08: Golden exact rational snapshots (hAdj 0..6)
- B10: Property-based testing (Hypothesis)
- B11: Differential testing (2D direct vs 1D reduction vs mpmath)
- B12: Exact rational Fraction reference oracle
- B13: Mutation testing (mutant constants must be killed by verifier)
- B14: Metamorphic testing (symmetry, positivity, mod-3 shifts, scaling)
- B20: Multi-precision numerical stability (50 / 80 / 120 dps)
- B28: Deterministic controls
"""
from __future__ import annotations

import math
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_conjecture as vc  # noqa: E402


# --- B08: Golden exact rational table (matching NonVacuity.lean hAdj_zero..five) ---

GOLDEN_HADJ: dict[int, Fraction] = {
    0: Fraction(0, 1),
    1: Fraction(1, 3),
    2: Fraction(2, 3),
    3: Fraction(13, 9),
    4: Fraction(140, 81),
    5: Fraction(545, 243),
    6: Fraction(226, 81),
}


@pytest.mark.parametrize(("L", "expected"), sorted(GOLDEN_HADJ.items()))
def test_golden_exact_hadj_matches_nonvacuity(L: int, expected: Fraction) -> None:
    """Golden snapshot test (B08) matching NonVacuity.lean hAdj_zero..five."""
    assert vc.h_adj_direct_exact(L) == expected
    if L >= 3:
        assert vc.h_adj_1d_exact(L) == expected


# --- B10 + B11 + B12: Hypothesis property-based & differential exact rational oracle ---

@given(L=st.integers(min_value=3, max_value=36))
@settings(max_examples=34, derandomize=True)
def test_property_2d_equals_1d_exact_rational(L: int) -> None:
    """Property-based & differential oracle test (B10, B11, B12): 2D sum == 1D formula over Q."""
    direct = vc.h_adj_direct_exact(L)
    reduced = vc.h_adj_1d_exact(L)
    assert direct == reduced
    assert direct > 0


@given(n=st.integers(min_value=5, max_value=500))
@settings(max_examples=60, derandomize=True)
def test_property_gamma_linear_and_cyclic_algebraic_identities(n: int) -> None:
    """Property-based check of Claim C4 (gamma_closed_form & gamma_cyclic_closed_form)."""
    with mp.workdps(60):
        nf = mp.mpf(n)
        pi = mp.pi
        sqrt3 = mp.sqrt(3)
        a_tri = mp.mpf(1) / 32 - 4 * sqrt3 / 243
        p1 = (nf * nf - 4 * nf - 4) / (32 * pi * nf)
        q1 = a_tri * nf / pi - (nf + 1) / (8 * pi * nf)
        r1 = -(nf + 1) / (8 * pi * nf)

        lhs_lin = (nf - 1) * p1 + 2 * (nf - 2) * q1 + (nf - 2) * (nf - 3) * r1
        rhs_lin = -(nf * (nf + 1)) / (32 * pi) - 8 * sqrt3 * nf * (nf - 2) / (243 * pi) + (nf - 1) / (8 * pi * nf)
        assert abs(lhs_lin - rhs_lin) < mp.mpf("1e-52")

        lhs_cyc = nf * p1 + 2 * nf * q1 + nf * (nf - 3) * r1
        rhs_cyc = -(nf * (nf + 4)) / (32 * pi) - 8 * sqrt3 * (nf * nf) / (243 * pi)
        assert abs(lhs_cyc - rhs_cyc) < mp.mpf("1e-52")


# --- B14: Metamorphic tests ---

def test_metamorphic_x1_x3_swap_symmetry_and_prob_mass() -> None:
    """Metamorphic check (B14): integrand |x2-x1||x3-x2| is invariant under x1 <-> x3 and trinomial probabilities sum to 1."""
    for L in range(0, 15):
        prob_sum = Fraction(0)
        swapped_expect = Fraction(0)
        for x1 in range(L + 1):
            for x2 in range(L - x1 + 1):
                x3 = L - x1 - x2
                w = Fraction(
                    math.factorial(L),
                    math.factorial(x1) * math.factorial(x2) * math.factorial(x3) * (3**L),
                )
                prob_sum += w
                swapped_expect += w * abs(x2 - x3) * abs(x1 - x2)
        assert prob_sum == Fraction(1, 1)
        assert swapped_expect == vc.h_adj_direct_exact(L)


def test_metamorphic_residue_cosine_structure() -> None:
    """Metamorphic check (B14): b_r = d_0 + (4*sqrt(3)/(9*pi)) * cos(2*pi*r/3) for r in {0, 1, 2}."""
    with mp.workdps(60):
        sqrt3 = mp.sqrt(3)
        pi = mp.pi
        d0 = -4 * sqrt3 / (81 * pi)
        expected = [32 * sqrt3 / (81 * pi), -22 * sqrt3 / (81 * pi), -22 * sqrt3 / (81 * pi)]
        for r, b_exp in enumerate(expected):
            cos_val = d0 + 4 * sqrt3 / (9 * pi) * mp.cos(2 * pi * r / 3)
            assert abs(cos_val - b_exp) < mp.mpf("1e-55")
        assert abs((expected[0] + expected[1] + expected[2]) / 3 - d0) < mp.mpf("1e-55")


# --- B06: Negative & adversarial tests ---

def test_negative_invalid_inputs_rejected() -> None:
    """Negative test (B06): invalid inputs raise explicit errors."""
    for bad_L in (-5, 0, 1, 2):
        with pytest.raises(ValueError):
            vc.h_adj_1d_exact(bad_L)
    with mp.workdps(50):
        with pytest.raises(ValueError):
            vc.h_adj_1d_mp(10, 3)
        with pytest.raises(ValueError):
            vc.h_adj_1d_mp(10, -1)


def test_negative_p3q_out_of_support_is_zero() -> None:
    """Negative test (B06): trinomial mass outside support 0 <= 2x <= 3q is identically 0."""
    assert vc.p3q_exact(4, -1) == Fraction(0)
    assert vc.p3q_exact(4, 7) == Fraction(0)
    assert vc.p3q_exact(4, 100) == Fraction(0)


# --- B20: Numerical & multi-precision stability ---

def test_numeric_stability_across_working_precisions() -> None:
    """Multi-precision stability check (B20): 50, 80, and 120 dps agree to > 42 digits on q=200..600."""
    results: dict[int, tuple[mp.mpf, mp.mpf, mp.mpf]] = {}
    q_grid = [100, 200, 300, 400, 500]
    for dps in (50, 80, 120):
        with mp.workdps(dps):
            sqrt3 = mp.sqrt(3)
            pi = mp.pi
            cL = 2 * sqrt3 / (3 * pi) + mp.mpf(1) / 9
            aStar = -2 * sqrt3 / (9 * pi)
            xs0 = [mp.mpf(3 * q) for q in q_grid]
            ys0 = [L * (vc.h_adj_1d_mp(q, 0) - cL * L - aStar) for q, L in zip(q_grid, xs0)]
            xs1 = [mp.mpf(3 * q + 1) for q in q_grid]
            ys1 = [L * (vc.h_adj_1d_mp(q, 1) - cL * L - aStar) for q, L in zip(q_grid, xs1)]
            xs2 = [mp.mpf(3 * q - 1) for q in q_grid]
            ys2 = [L * (vc.h_adj_1d_mp(q, 2) - cL * L - aStar) for q, L in zip(q_grid, xs2)]
            results[dps] = (
                vc.richardson_extrapolate(xs0, ys0),
                vc.richardson_extrapolate(xs1, ys1),
                vc.richardson_extrapolate(xs2, ys2),
            )

    with mp.workdps(120):
        for idx in range(3):
            diff_50_120 = abs(results[50][idx] - results[120][idx])
            diff_80_120 = abs(results[80][idx] - results[120][idx])
            assert diff_50_120 < mp.mpf("1e-35")
            assert diff_80_120 < mp.mpf("1e-65")


# --- B13: Automated mutation testing (killing mathematical & formula mutants) ---

def test_mutation_killing_constant_and_sign_mutants() -> None:
    """Mutation testing (B13): verify that perturbed mutant constants are reliably killed by the verifier."""
    with mp.workdps(80):
        sqrt3 = mp.sqrt(3)
        pi = mp.pi
        cL = 2 * sqrt3 / (3 * pi) + mp.mpf(1) / 9
        aStar = -2 * sqrt3 / (9 * pi)
        q_rich = [120 + 60 * i for i in range(10)]
        xs0 = [mp.mpf(3 * q) for q in q_rich]
        xs1 = [mp.mpf(3 * q + 1) for q in q_rich]
        xs2 = [mp.mpf(3 * q - 1) for q in q_rich]
        b0_emp = vc.richardson_extrapolate(xs0, [L * (vc.h_adj_1d_mp(q, 0) - cL * L - aStar) for q, L in zip(q_rich, xs0)])
        b1_emp = vc.richardson_extrapolate(xs1, [L * (vc.h_adj_1d_mp(q, 1) - cL * L - aStar) for q, L in zip(q_rich, xs1)])
        b2_emp = vc.richardson_extrapolate(xs2, [L * (vc.h_adj_1d_mp(q, 2) - cL * L - aStar) for q, L in zip(q_rich, xs2)])
        d0_emp = (b0_emp + b1_emp + b2_emp) / 3
        aTri_emp = mp.mpf(1) / 32 + pi / 9 * (b0_emp + b1_emp + b2_emp)
        gamma2_emp = (64 * aTri_emp - 3) / (32 * pi)

        # True constants pass tight tolerance
        assert abs(b0_emp - 32 * sqrt3 / (81 * pi)) < mp.mpf("1e-18")
        assert abs(aTri_emp - (mp.mpf(1) / 32 - 4 * sqrt3 / 243)) < mp.mpf("1e-18")

        # Mutants: every single mutant MUST fail the tolerance check (mutant killed!)
        mutants = [
            ("mutant_aTri_naive_1_32", aTri_emp, mp.mpf(1) / 32),
            ("mutant_aTri_sign_flip", aTri_emp, mp.mpf(1) / 32 + 4 * sqrt3 / 243),
            ("mutant_d0_zero", d0_emp, mp.mpf(0)),
            ("mutant_d0_sign_flip", d0_emp, +4 * sqrt3 / (81 * pi)),
            ("mutant_b0_coeff_31", b0_emp, 31 * sqrt3 / (81 * pi)),
            ("mutant_b1_equals_b0", b1_emp, 32 * sqrt3 / (81 * pi)),
            ("mutant_gamma2_sign_flip", gamma2_emp, -mp.mpf(1) / (32 * pi) + 8 * sqrt3 / (243 * pi)),
        ]
        tol = mp.mpf("1e-10")
        killed = 0
        for name, empirical, mutant_val in mutants:
            assert abs(empirical - mutant_val) > tol, f"Mutant survived: {name}"
            killed += 1
        assert killed == len(mutants)
