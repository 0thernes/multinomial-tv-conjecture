#!/usr/bin/env python3
"""
Generate publication-grade vector PDF figures for:
  "Proof and Lean 4 Verification of Conjecture 7.7 on the Second-Order
   Variance of Multinomial Discrete Total Variation"

Usage:
    uv run --with matplotlib --with mpmath --with numpy python scripts/generate_figures.py
"""

from __future__ import annotations

from pathlib import Path
import numpy as np
import mpmath as mp
import matplotlib as mpl
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

# Configure Annals-grade serif / Computer Modern typography
mpl.rcParams.update(
    {
        "font.family": "serif",
        "font.serif": ["CMU Serif", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "axes.labelsize": 10.5,
        "axes.titlesize": 11,
        "xtick.labelsize": 9,
        "ytick.labelsize": 9,
        "legend.fontsize": 8.5,
        "axes.linewidth": 0.8,
        "xtick.major.width": 0.7,
        "ytick.major.width": 0.7,
        "xtick.direction": "in",
        "ytick.direction": "in",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)

# Colorblind-safe Okabe-Ito academic palette
C_BLUE = "#0072B2"
C_VERM = "#D55E00"
C_TEAL = "#009E73"
C_PURP = "#7A5195"
C_GRAY = "#4D4D4D"
C_GOLD = "#CC79A7"


def sums_abc_mp(q: int) -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    log_p0 = mp.loggamma(3 * q + 1) - (3 * q) * mp.log(3) - 3 * mp.loggamma(q + 1)
    p0 = mp.exp(log_p0)
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
        A += rp - rm
        B += u * (rp + rm)
        C += (u * u) * (rp - rm)
        if k > 20 and abs(rp) < mp.mpf("1e-50") and abs(rm) < mp.mpf("1e-50"):
            break
    return p0, A, B, C


def h_adj_from_abc(q: int, r: int, p0: mp.mpf, A: mp.mpf, B: mp.mpf, C: mp.mpf) -> mp.mpf:
    qf = mp.mpf(q)
    if r == 0:
        return (3 * qf) / 9 + 2 * qf * p0 * (1 + A - 2 * B) + 4 * qf * qf * p0
    elif r == 1:
        return (
            (3 * qf + 1) / 9
            + (2 * (3 * qf + 1) / 3) * p0 * A
            + (2 * (6 * qf + 1) * (3 * qf + 1) / 9) * p0
        )
    else:
        return (
            (3 * qf - 1) / 9
            + 2 * qf * p0 * ((1 - 1 / qf) * (1 + A) - (4 - 2 / qf) * B + 4 * C)
            + 4 * qf * qf * p0
        )


def make_fig1(out_path: Path) -> None:
    mp.mp.dps = 50
    sqrt3 = mp.sqrt(3)
    pi = mp.pi
    cL = 2 * sqrt3 / (3 * pi) + mp.mpf(1) / 9
    aStar = -2 * sqrt3 / (9 * pi)
    b0_ex = 32 * sqrt3 / (81 * pi)
    b1_ex = -22 * sqrt3 / (81 * pi)
    d0_ex = -4 * sqrt3 / (81 * pi)

    # Panel (a): L up to 180
    qs_a = list(range(2, 61))
    L0_a, y0_a = [], []
    L1_a, y1_a = [], []
    L2_a, y2_a = [], []
    for q in qs_a:
        p0, A, B, C = sums_abc_mp(q)
        L0, L1, L2 = 3 * q, 3 * q + 1, 3 * q - 1
        L0_a.append(L0)
        y0_a.append(float(L0 * (h_adj_from_abc(q, 0, p0, A, B, C) - cL * L0 - aStar)))
        L1_a.append(L1)
        y1_a.append(float(L1 * (h_adj_from_abc(q, 1, p0, A, B, C) - cL * L1 - aStar)))
        L2_a.append(L2)
        y2_a.append(float(L2 * (h_adj_from_abc(q, 2, p0, A, B, C) - cL * L2 - aStar)))

    # Panel (b): log-log error decay up to q = 3000
    qs_b = [5, 8, 12, 20, 35, 60, 100, 180, 300, 500, 1000, 1800, 3000]
    Ls_b = []
    e0_b, e1_b, e2_b = [], [], []
    eA_b, eB_b, eC_b = [], [], []
    for q in qs_b:
        p0, A, B, C = sums_abc_mp(q)
        L0, L1, L2 = 3 * q, 3 * q + 1, 3 * q - 1
        Ls_b.append(L0)
        e0_b.append(float(abs(L0 * (h_adj_from_abc(q, 0, p0, A, B, C) - cL * L0 - aStar) - b0_ex)))
        e1_b.append(float(abs(L1 * (h_adj_from_abc(q, 1, p0, A, B, C) - cL * L1 - aStar) - b1_ex)))
        e2_b.append(float(abs(L2 * (h_adj_from_abc(q, 2, p0, A, B, C) - cL * L2 - aStar) - b1_ex)))
        eA_b.append(float(abs(q * (A - (-mp.mpf(1) / 9 - mp.mpf(4) / (243 * q))))))
        eB_b.append(float(abs(q * (B - (mp.mpf(1) / 3 - mp.mpf(2) / (27 * q))))))
        eC_b.append(float(abs(q * (C - (-mp.mpf(2) / (27 * q))))))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.05))
    fig.subplots_adjust(wspace=0.28, bottom=0.15, top=0.88, left=0.08, right=0.98)

    # Panel (a)
    ax1.axhline(float(b0_ex), color=C_BLUE, lw=1.0, ls="--", alpha=0.85)
    ax1.axhline(float(b1_ex), color=C_VERM, lw=1.0, ls="--", alpha=0.85)
    ax1.axhline(float(d0_ex), color=C_GRAY, lw=0.9, ls=":", alpha=0.85)

    ax1.plot(L0_a, y0_a, color=C_BLUE, lw=1.5, marker="o", ms=2.6, markevery=3,
             label=r"$\ell \equiv 0\ (\mathrm{mod}\ 3)$")
    ax1.plot(L1_a, y1_a, color=C_VERM, lw=1.5, marker="s", ms=2.5, markevery=3,
             label=r"$\ell \equiv 1\ (\mathrm{mod}\ 3)$")
    ax1.plot(L2_a, y2_a, color=C_TEAL, lw=1.2, ls="-.", marker="^", ms=2.6, markevery=3,
             label=r"$\ell \equiv 2\ (\mathrm{mod}\ 3)$")

    ax1.text(177, float(b0_ex) + 0.014,
             r"$b_0 = \frac{32\sqrt{3}}{81\pi} \approx +0.2178$",
             ha="right", va="bottom", fontsize=8.5, color=C_BLUE)
    ax1.text(8, float(d0_ex) + 0.012,
             r"$d_0 = -\frac{4\sqrt{3}}{81\pi} \approx -0.0272$",
             ha="left", va="bottom", fontsize=8.5, color=C_GRAY)
    ax1.text(177, float(b1_ex) - 0.016,
             r"$b_1 = b_2 = -\frac{22\sqrt{3}}{81\pi} \approx -0.1497$",
             ha="right", va="top", fontsize=8.5, color=C_VERM)

    ax1.set_xlim(0, 185)
    ax1.set_ylim(-0.24, 0.30)
    ax1.set_xlabel(r"Three-bin total $\ell$")
    ax1.set_ylabel(r"$\ell\,(h_{\mathrm{adj}}(\ell) - c_L \ell - a_*)$")
    ax1.set_title(r"(a) Convergence by residue class $\ell\ \mathrm{mod}\ 3$")
    ax1.legend(loc="center right", bbox_to_anchor=(0.98, 0.56), frameon=True,
               framealpha=0.95, edgecolor="#CCCCCC")
    ax1.grid(True, lw=0.35, alpha=0.45)

    # Panel (b)
    ax2.loglog(Ls_b, e0_b, color=C_BLUE, lw=1.5, marker="o", ms=3.5,
               label=r"$|b_0(\ell) - b_0|$")
    ax2.loglog(Ls_b, e1_b, color=C_VERM, lw=1.5, marker="s", ms=3.3,
               label=r"$|b_1(\ell) - b_1|$")
    ax2.loglog(Ls_b, e2_b, color=C_TEAL, lw=1.2, ls="--", marker="^", ms=3.2,
               label=r"$|b_2(\ell) - b_2|$")
    ax2.loglog(Ls_b, eB_b, color=C_PURP, lw=1.2, ls=":", marker="d", ms=3.0,
               label=r"$q\,|B(q) - (\frac{1}{3}-\frac{2}{27q})|$")

    # Reference O(L^-1) guide line
    ref_x = np.array([25.0, 8000.0])
    ref_y = 0.35 / ref_x
    ax2.loglog(ref_x, ref_y, color=C_GRAY, lw=0.9, ls="-.")
    ax2.text(280, 0.35 / 280 * 1.45, r"slope $-1$ ($O(\ell^{-1})$)",
             fontsize=8.3, color=C_GRAY, rotation=-27)

    ax2.set_xlabel(r"Three-bin total $\ell = 3q$")
    ax2.set_ylabel(r"Absolute asymptotic residual")
    ax2.set_title(r"(b) Residual decay across three decades")
    ax2.legend(loc="lower left", frameon=True, framealpha=0.92, edgecolor="#CCCCCC")
    ax2.grid(True, which="major", lw=0.35, alpha=0.45)

    fig.savefig(out_path, format="pdf")
    plt.close(fig)
    print(f"Wrote {out_path}")


def make_fig2(out_path: Path) -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.1))
    fig.subplots_adjust(wspace=0.28, bottom=0.15, top=0.88, left=0.06, right=0.98)

    # Panel (a): Barycentric 2D-to-1D simplex reduction diagram
    # Vertices of equilateral triangle: V1=(0,0), V2=(1,0), V3=(0.5, sqrt(3)/2)
    h_tri = np.sqrt(3) / 2.0
    V1 = np.array([0.0, 0.0])       # (L, 0, 0)
    V2 = np.array([1.0, 0.0])       # (0, L, 0)
    V3 = np.array([0.5, h_tri])     # (0, 0, L)
    M12 = 0.5 * (V1 + V2)           # (L/2, L/2, 0)
    M23 = 0.5 * (V2 + V3)           # (0, L/2, L/2)
    M31 = 0.5 * (V3 + V1)           # (L/2, 0, L/2)
    C0 = (V1 + V2 + V3) / 3.0       # (q, q, q)

    def bary(a: float, b: float, c: float) -> np.ndarray:
        return a * V1 + b * V2 + c * V3

    # Full simplex outline
    tri = Polygon([V1, V2, V3], closed=True, facecolor="#F7F8FA", edgecolor="#222222", lw=1.2)
    ax1.add_patch(tri)

    # Highlight strict wedge a < b < c: vertices are V3 (0,0,1), M23 (0,1/2,1/2), C0 (1/3,1/3,1/3)
    wedge = Polygon(
        [V3, M23, C0],
        closed=True,
        facecolor="#D9EAF7",
        edgecolor=C_BLUE,
        lw=1.3,
        zorder=2,
    )
    ax1.add_patch(wedge)

    # Six Weyl chamber medians (x1=x2, x2=x3, x3=x1)
    for P, Q in [(V3, M12), (V1, M23), (V2, M31)]:
        ax1.plot([P[0], Q[0]], [P[1], Q[1]], color="#777777", lw=0.85, ls="--", zorder=3)

    # Highlight the 1D central slice x1 = x2 = x, x3 = 3q - 2x (segment from V3 to M12)
    ax1.plot([V3[0], C0[0]], [V3[1], C0[1]], color=C_VERM, lw=2.4, zorder=5,
             label=r"Left branch $x < q$ ($-p_{3q}(x)$)")
    ax1.plot([C0[0], M12[0]], [C0[1], M12[1]], color=C_TEAL, lw=2.4, zorder=5,
             label=r"Right branch $x > q$ ($+p_{3q}(x)$)")

    # Show telescoping arrows inside the wedge a < b < c toward the boundary
    for a_frac in [0.06, 0.14, 0.22]:
        b_start = a_frac + 0.03
        b_end = (1.0 - a_frac) / 2.0 - 0.02
        p_s = bary(a_frac, b_start, 1.0 - a_frac - b_start)
        p_e = bary(a_frac, b_end, 1.0 - a_frac - b_end)
        ax1.annotate(
            "",
            xy=p_e,
            xytext=p_s,
            arrowprops=dict(arrowstyle="->", color=C_BLUE, lw=0.95, shrinkA=0, shrinkB=0),
            zorder=4,
        )

    # Center point (q, q, q)
    ax1.scatter([C0[0]], [C0[1]], color="#111111", s=36, zorder=6)
    ax1.annotate(
        r"$(q,q,q)$",
        xy=(C0[0] - 0.01, C0[1] - 0.01),
        xytext=(0.30, 0.25),
        ha="right", va="center", fontsize=8.8,
        bbox=dict(facecolor="white", edgecolor="none", pad=1.0, alpha=0.85),
        arrowprops=dict(arrowstyle="->", color="#444444", lw=0.75),
        zorder=7,
    )

    # Labels
    ax1.text(V1[0] - 0.02, V1[1] - 0.03, r"$(\ell,0,0)$", ha="left", va="top", fontsize=8.5)
    ax1.text(V2[0] + 0.02, V2[1] - 0.03, r"$(0,\ell,0)$", ha="right", va="top", fontsize=8.5)
    ax1.text(V3[0], V3[1] + 0.025, r"$(0,0,\ell)$", ha="center", va="bottom", fontsize=8.5)
    ax1.annotate(
        r"Strict wedge" + "\n" + r"$a < b < c$",
        xy=(0.64, 0.49),
        xytext=(0.89, 0.67),
        ha="center", va="center",
        fontsize=8.3, color=C_BLUE, fontweight="bold",
        arrowprops=dict(arrowstyle="->", color=C_BLUE, lw=0.9),
        zorder=7,
    )
    ax1.text(0.16, 0.62, r"$S_3$ symmetry" + "\n(6 chambers)", ha="center", va="center",
             fontsize=8.2, color=C_GRAY)

    ax1.set_xlim(-0.08, 1.09)
    ax1.set_ylim(-0.18, h_tri + 0.10)
    ax1.set_aspect("equal")
    ax1.axis("off")
    ax1.set_title(r"(a) Exact 2D-to-1D simplex reduction ($\Delta_\ell \to x_1 = x_2$)")
    ax1.legend(loc="lower center", bbox_to_anchor=(0.5, -0.05), ncol=1,
               frameon=True, framealpha=0.96, edgecolor="#CCCCCC", fontsize=7.9)

    # Panel (b): Local Gaussian asymmetry & cutoff K_q = floor(q^{5/8})
    q_demo = 120
    eps = 1.0 / np.sqrt(q_demo)
    K_cut = int(np.floor(q_demo ** (5.0 / 8.0)))  # 19 for q=120 -> t_cut ~ 1.73
    t_cut = K_cut * eps

    # Compute exact normalized ratios r_+(k) and r_-(k) for k = 1..30
    ks = np.arange(1, 30)
    ts = ks * eps
    rp_arr = np.zeros_like(ts)
    rm_arr = np.zeros_like(ts)
    rp, rm = 1.0, 1.0
    for idx, k in enumerate(ks):
        rp = rp * (q_demo - 2 * k + 2) * (q_demo - 2 * k + 1) / ((q_demo + k) ** 2)
        rm = rm * ((q_demo - k + 1) ** 2) / ((q_demo + 2 * k - 1) * (q_demo + 2 * k))
        rp_arr[idx] = rp
        rm_arr[idx] = rm

    t_dense = np.linspace(0.0, 2.55, 300)
    sym_exact = ts * (rp_arr + rm_arr) / 2.0
    sym_gauss = t_dense * np.exp(-3.0 * t_dense**2)
    skew_exact = -(rp_arr - rm_arr) / (2.0 * eps)
    skew_gauss = (t_dense**3) * np.exp(-3.0 * t_dense**2)

    # Shaded tail region t > t_cut
    ax2.axvspan(t_cut, 2.6, color="#F2E5E5", alpha=0.55, zorder=0)
    ax2.axvline(t_cut, color=C_VERM, lw=1.0, ls=":", zorder=2)
    ax2.text(t_cut + 0.05, 0.145,
             r"Tail $k > K_q = \lfloor q^{5/8}\rfloor$" + "\n" + r"($\leq C\,e^{-q^{1/4}/3}$)",
             fontsize=8.0, color=C_VERM, va="center", ha="left")

    ax2.plot(t_dense, sym_gauss, color=C_BLUE, lw=1.4,
             label=r"Leading $B(q)$ kernel: $t\,e^{-3t^2}$")
    ax2.scatter(ts, sym_exact, color=C_BLUE, s=16, zorder=4,
                label=r"Exact $\frac{t}{2}\frac{p_{3q}(q+k)+p_{3q}(q-k)}{p_{3q}(q)}$ ($q=120$)")

    ax2.plot(t_dense, skew_gauss, color=C_TEAL, lw=1.4, ls="--",
             label=r"Leading $A(q)$ skew: $t^3 e^{-3t^2}$")
    ax2.scatter(ts, skew_exact, color=C_TEAL, marker="s", s=14, zorder=4,
                label=r"Exact $-\frac{\sqrt{q}}{2}\frac{p_{3q}(q+k)-p_{3q}(q-k)}{p_{3q}(q)}$")

    # Annotate the Euler-Maclaurin origin slope g'(0)=1 giving -h^2/12
    ax2.annotate(
        r"$g_0'(0) = 1 \Rightarrow -\frac{h^2}{12}$" + "\nEuler–Maclaurin shift",
        xy=(0.09, 0.088),
        xytext=(0.76, 0.175),
        fontsize=7.9,
        color="#222222",
        bbox=dict(facecolor="white", edgecolor="#DDDDDD", pad=2.5, alpha=0.92),
        arrowprops=dict(arrowstyle="->", color="#333333", lw=0.85, connectionstyle="arc3,rad=0.14"),
        zorder=6,
    )

    ax2.set_xlim(0.0, 2.55)
    ax2.set_ylim(-0.015, 0.40)
    ax2.set_xlabel(r"Rescaled lattice coordinate $t = k/\sqrt{q}$")
    ax2.set_ylabel(r"Normalized local summand")
    ax2.set_title(r"(b) Local odd-Gaussian profiles and cutoff $K_q$")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.93, edgecolor="#CCCCCC", fontsize=7.6)
    ax2.grid(True, lw=0.35, alpha=0.45)

    fig.savefig(out_path, format="pdf")
    plt.close(fig)
    print(f"Wrote {out_path}")


def main() -> None:
    fig_dir = Path(__file__).resolve().parent.parent / "paper" / "figures"
    fig_dir.mkdir(parents=True, exist_ok=True)
    make_fig1(fig_dir / "fig1_residue_convergence.pdf")
    make_fig2(fig_dir / "fig2_reduction_gaussian.pdf")


if __name__ == "__main__":
    main()
