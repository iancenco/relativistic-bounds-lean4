# Relativistic Stellar & Continuum Bounds in Lean 4

[![Lean 4 Verify](https://github.com/iancenco/relativistic-bounds-lean4/actions/workflows/lean.yml/badge.svg)](https://github.com/iancenco/relativistic-bounds-lean4/actions/workflows/lean.yml)

**Author:** Serghei Iancenco  
**Methodology:** AI-assisted mathematical-physics research, exact-arithmetic certification, Lean 4 formalization, and cross-model statement auditing (directed by the author).

Machine-checked **Lean 4.36.0 + Mathlib** formalization of an equation-of-state-independent lower bound on the slow-rotation moment of inertia of relativistic stars, checked with zero `sorry`, zero `native_decide`, and standard axioms only.

---

## Manuscript & Files

- **Standalone Paper (PDF):** [`paper/kerr_inertia_floor.pdf`](paper/kerr_inertia_floor.pdf)
- **Standalone Paper (LaTeX source):** [`paper/kerr_inertia_floor.tex`](paper/kerr_inertia_floor.tex)
- **Lean 4 Proof:** [`NaturalMechanics/T4A18_KerrInertia.lean`](NaturalMechanics/T4A18_KerrInertia.lean) (`1,576` lines)
- **Statement & Physics Audit:** [`AUDIT-T4A18.md`](AUDIT-T4A18.md)

---

## Theorem: Equation-of-State-Independent Kerr Lower Bound (`I > 4 M³`)

### Physical Statement (`G = c = 1`)

Let `(m, ε, p, Z)` be a static, spherically symmetric, horizonless, isotropic perfect-fluid star of radius `R > 0` and total mass `M = m(R) > 0`, rigidly and slowly rotating to first order in Hartle's framework, obeying:
1. **Reduced Einstein–TOV and Hartle (1967) slow-rotation equations** off an arbitrary finite set of radial interfaces `jumps : Finset ℝ` (allowing finitely many first-order interior density discontinuities and a surface density jump), with continuous Israel–Darmois junction matching of `m`, `p`, and the Hartle frame-dragging variable `Z = r s ω̄'/ω̄` across every interface, and weighted central regularity limits `m/r → 0`, `4π r² p → 0`, `Z → 0` as `r → 0⁺`;
2. **Non-increasing mean energy density** (`4π r³ ε(r) ≤ 3 m(r)` on `(0, R]`), which is strictly weaker than—and implied by (Lemma 1 in the paper)—**non-increasing local energy density** (`AntitoneOn ε (0, R]`), with no assumed nuclear equation of state and no subluminal sound-speed condition;
3. **Isotropic Dominant Energy Condition (`0 ≤ p ≤ ε`)** and vacuum surface boundary `p(R) = 0`.

Then:
- **Auxiliary compactness lemma (Bondi–Pontryagin DEC bound):** `m(r)/r < 51/125 = 0.408` for every `r ∈ (0, R]` (so `s(r)² = 1 − 2 m(r)/r > 23/125`).
- **Moment-of-inertia lower bound:** The exterior Hartle moment of inertia `I = R³ Z(R) / (6 s(R) + 2 Z(R))` strictly exceeds the slow-rotation Kerr black-hole value `I_Kerr = 4 M³`:

```math
I \;>\; 4 M^3 \;=\; I_{\mathrm{Kerr}}.
```

### Main Lean 4 Signatures

*(Module `NaturalMechanics/T4A18_KerrInertia.lean`, namespace `NaturalMechanics.T4A18`; internal identifiers are retained for commit and CI stability.)*

```lean
theorem MonotoneIsotropicDECStar.t4a18_unconditional_kerr_inertia_floor
    (S : MonotoneIsotropicDECStar) : S.I > 4 * S.M ^ 3

theorem t4a18_kerr_inertia_floor_of_antitone_piecewise
    (S : PiecewiseRegularIsotropicDECStar) (hε : AntitoneOn S.ε (Ioc 0 S.R)) :
    S.R ^ 3 * S.Z S.R / (6 * sFun S.m S.R + 2 * S.Z S.R) > 4 * S.m S.R ^ 3

theorem MonotoneIsotropicDECStar.compactness_wall
    (S : MonotoneIsotropicDECStar) : ∀ r ∈ Ioc 0 S.R, S.m r / r < 51 / 125
```

### Proof Architecture

1. **Part A (`partA`):** Exact shifted Hartle–TOV Riccati identity for `W_α = Z − 2α π_p / s` against the Schwarzschild vacuum curve `Z_c(s) = 3 Ī₀ s (1 − s²)³ / (4 − Ī₀ (1 − s²)³)`, proving that both the matter-free term and the `π_e π_p` cross term vanish identically for arbitrary `(α, Ī₀)`.
2. **Part B (`compactness_wall`):** Auxiliary two-piece Bondi–Pontryagin polynomial barrier (`u_j = 49/200`) proving `m(r)/r < 51/125` across arbitrary finite density jumps, with all polynomial positivity inequalities discharged by exact rational Bernstein certificates (zero floating-point arithmetic).
3. **Part C (`t4a18_unconditional_kerr_inertia_floor`):** At `α = 69/100`, `Ī₀ = 4`, single-interval exact rational Bernstein certificates discharge `c_e > 0` and `c_e + c_p > 0` on `s² ∈ [23/125, 1]`, propagating a strict exponential barrier across any finite set of density jumps from the centre to the surface `p(R) = 0`, yielding `Z(R) > Z_c(s(R))` and hence `I > 4 M³`.

---

## Scope, Sharpness, and Literature Context

Full details, citations, and numerical benchmarks are given in Sections 1, 4, and 5 of [`paper/kerr_inertia_floor.pdf`](paper/kerr_inertia_floor.pdf):

- **Prior art on inertia bounds:** Sabbadini & Hartle (1977) and Hartle (1978, Sec. 5.3.2) established variational bounds on `M` and `I` assuming a known low-density nuclear equation of state below a matching density `ρ_0` plus causality (`dp/dε ≤ 1`). More recently, Barta & Gergely (Nov 2026) numerically checked `I/M³ > 4` across four nuclear equations of state. The present theorem requires no low-density EOS and no causality assumption.
- **Auxiliary compactness lemma vs. literature:** The bound `m(r)/r < 51/125 = 0.408` is an auxiliary lemma sufficient to keep `s² > 23/125` for Part C, not a sharp compactness record (cf. Buchdahl 1959, Bondi 1964, Barraco & Hamity 2002, Karageorgis & Stalker 2008, Andréasson 2008). Note that while *uniform-density* DEC stars obey `M/R ≤ 3/8 = 0.375`, non-uniform monotone isotropic DEC stars (such as a `p = ε` core continuously matched to a constant-density envelope) attain `M/R = 0.398800 > 3/8`, placing `51/125 = 0.408` within `2.3%` of explicit monotone DEC attainment.
- **Sharpness:** The constant `4` is the exact Kerr black-hole benchmark, **not** the sharp infimum of the monotone DEC isotropic class. Direct coupled Hartle–TOV integrations give `I/M³ = 4.6549` for uniform stars at the DEC limit `C = 3/8`, `I/M³ = 4.2855` for extremal two-zone monotone DEC stars (`C = 0.3958`), and `I/M³ → 4.0459` at the uniform Buchdahl limit (`C → 4/9`, violating DEC; Chandrasekhar & Miller 1974, Posada 2017). The same barrier extends beyond DEC up to `0 ≤ p ≤ 1.1556 ε`; whether `I > 4 M³` holds for the full Buchdahl class (arbitrary `p ≥ 0`, no DEC) remains open.
- **Necessity of isotropy:** Relaxing pressure isotropy (`p_t ≠ p_r`) allows strictly-DEC relativistic stars to drop below the Kerr value (`I/M³ ≈ 3.74 < 4`), showing that the isotropic hypothesis cannot be dropped without a lower bound on `p_t`.
- **Formalization boundary & non-vacuity:** Lean takes the reduced TOV/Hartle ODEs, weighted central limits, and matched surface formula as structure fields; their derivation from the 4D Einstein equations is given in Section 2 of the paper. Explicit smooth (`C = 1/10` Schwarzschild interior) and two-layer discontinuous (`jumps = {1/2, 1}`) physical witnesses satisfying every Lean field are proved mathematically in Section 4 of the paper and [`AUDIT-T4A18.md`](AUDIT-T4A18.md), but formalizing `Nonempty MonotoneIsotropicDECStar` inside Lean 4 remains future work.

---

## Building and Checking Locally

Requires [Elan](https://github.com/leanprover/elan) (Lean 4 toolchain manager):

```bash
git clone https://github.com/iancenco/relativistic-bounds-lean4.git
cd relativistic-bounds-lean4
lake exe cache get
lake build
```

With the prebuilt Mathlib cache fetched, `lake build` compiles `NaturalMechanics.T4A18_KerrInertia` in ~15–20 seconds. GitHub Actions CI checks compilation, prohibited tokens (`sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, `native_decide`, `@[extern]`), and `#print axioms` (`[propext, Classical.choice, Quot.sound]`) on every push.

### Optional Python Scripts

- [`scripts/t4a18_bernstein_certs.py`](scripts/t4a18_bernstein_certs.py) — regenerates the exact rational Bernstein certificates embedded in `T4A18_KerrInertia.lean` (requires `sympy`).
- [`scripts/verify_t4a18_kerr_inertia_floor.py`](scripts/verify_t4a18_kerr_inertia_floor.py) — standalone exact-Sturm / exact-Bernstein Python verification script accompanying the continuum proof (`python scripts/verify_t4a18_kerr_inertia_floor.py`, requires `sympy`, `numpy`, `scipy`).

---

## Authorship & AI-Assisted Workflow

This repository is authored and maintained by **Serghei Iancenco**. Continuum certificate search, Lean 4.36.0 formalization, and cross-model statement auditing were carried out via an **AI-assisted multi-model workflow** directed by the author:

1. **Proof Development & Exact Certification:** Models assist in synthesizing exact rational algebraic and Bernstein positivity certificates rather than relying on floating-point numerics.
2. **Lean 4 Formalization:** Translates the certified continuum proof into zero-`sorry` Lean 4 + Mathlib code.
3. **Statement & Physics Audit:** A separate model audits the formalized definitions for physics faithfulness, axiom usage, and non-vacuity ([`AUDIT-T4A18.md`](AUDIT-T4A18.md)), which caught an initial omission of interior density jumps before the jump-inclusive revision.

Logical soundness of the formalized theorems depends strictly on the Lean 4 kernel and the three standard axioms `[propext, Classical.choice, Quot.sound]`. Physical faithfulness of the encoded assumptions and novelty relative to existing literature should be judged directly from [`paper/kerr_inertia_floor.pdf`](paper/kerr_inertia_floor.pdf), [`NaturalMechanics/T4A18_KerrInertia.lean`](NaturalMechanics/T4A18_KerrInertia.lean), and [`AUDIT-T4A18.md`](AUDIT-T4A18.md); human physicist review and corrections are welcomed via Issues or PRs.

---

## License

MIT — see [`LICENSE`](LICENSE).
