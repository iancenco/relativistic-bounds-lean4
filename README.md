# Relativistic Stellar & Continuum Bounds in Lean 4

[![Lean 4 Verify](https://github.com/iancenco/relativistic-bounds-lean4/actions/workflows/lean.yml/badge.svg)](https://github.com/iancenco/relativistic-bounds-lean4/actions/workflows/lean.yml)

**Author:** Serghei Iancenco  
**Methodology:** AI-assisted mathematical-physics research, exact-arithmetic certification, Lean 4 formalization, and cross-model statement auditing (directed by the author).

Machine-checked **Lean 4.36.0 + Mathlib** formalizations of equation-of-state-independent bounds in General Relativity and relativistic continuum mechanics, checked with zero `sorry` and standard axioms only.

---

## Theorem: Moment-of-Inertia Lower Bound (`I > 4 M³`)

**File:** [`NaturalMechanics/T4A18_KerrInertia.lean`](NaturalMechanics/T4A18_KerrInertia.lean) (`1,576` lines)  
**Statement & Physics Audit:** [`AUDIT-T4A18.md`](AUDIT-T4A18.md)

### Physical Statement (`G = c = 1`)

Let `(m, ε, p, Z)` be any regular, horizonless, static, spherically symmetric isotropic relativistic star of radius `R > 0` and total mass `M = m(R) > 0` obeying:
1. **Einstein–TOV + Hartle (1967) slow-rotation equations** off an arbitrary finite set of radial interfaces `jumps : Finset ℝ` (allowing arbitrary finite first-order interior density jumps as well as a surface density jump), with continuous junction matching of `m`, `p`, and the Hartle frame-dragging variable `Z = r s ω̄'/ω̄` across every interface;
2. **Non-increasing energy density** (`AntitoneOn ε (0, R]`, or equivalently non-increasing mean density `m(r)/r³`), with no equation-of-state or sound-speed causality assumption;
3. **Dominant Energy Condition (`0 ≤ p ≤ ε`)** and vacuum surface boundary `p(R) = 0`.

Then:
- **Compactness bound (Bondi–Pontryagin DEC bound):** `m(r)/r < 51/125 = 0.408` for every `r ∈ (0, R]` (so `s(r)² = 1 − 2 m(r)/r > 23/125`).
- **Moment-of-inertia bound:** The exterior Hartle moment of inertia `I = R³ Z(R) / (6 s(R) + 2 Z(R))` strictly exceeds the Kerr black-hole value `I_Kerr = 4 M³`:

```math
I \;>\; 4 M^3 \;=\; I_{\mathrm{Kerr}}.
```

### Main Lean 4 Signatures (`namespace NaturalMechanics.T4A18`)

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

1. **Part A (`partA`):** Exact shifted Hartle–TOV Riccati identity for `W_α = Z − 2α π_p / s` against the Schwarzschild vacuum curve `Z_c(s) = 3 Ī₀ s (1 − s²)³ / (4 − Ī₀ (1 − s²)³)`, proving that both the constant term and the `π_e π_p` cross term vanish identically for arbitrary `(α, Ī₀)`.
2. **Part B (`compactness_wall`):** Exact two-piece Bondi–Pontryagin differential barrier (`u_j = 49/200`) proving `m(r)/r < 51/125` across arbitrary finite density jumps, with all polynomial sign inequalities discharged by exact rational Bernstein positivity certificates (zero floating-point arithmetic).
3. **Part C (`t4a18_unconditional_kerr_inertia_floor`):** At `α = 69/100`, `Ī₀ = 4`, exact rational Bernstein certificates discharge `c_e > 0` and `c_e + c_p > 0` across `s² ∈ [23/125, 1]`, propagating a strict exponential barrier across any finite set of density jumps from the centre to the surface `p(R) = 0`, yielding `Z(R) > Z_c(s(R))` and hence `I > 4 M³`.

### Verification and Audit Notes

- **Toolchain:** `leanprover/lean4:v4.36.0` + `mathlib v4.36.0`
- **Axioms:** `#print axioms` returns `[propext, Classical.choice, Quot.sound]` for every theorem (checked in CI on every push).
- **Escape hatches:** No `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, `native_decide`, or `@[extern]`.
- **Statement & physics audit ([`AUDIT-T4A18.md`](AUDIT-T4A18.md)):** A separate review pass checked the signs and coefficients of the TOV and Hartle equations, constructed explicit analytic smooth (`C = 1/10` Schwarzschild interior) and two-layer discontinuous-density (`jumps = {1/2, 1}`) physical witnesses satisfying the Lean structure fields, caught an initial scope omission of interior density jumps, and re-checked the `PiecewiseRegularIsotropicDECStar` revision. *(As noted in `AUDIT-T4A18.md`, non-vacuity / inhabitance of `MonotoneIsotropicDECStar` is checked mathematically outside Lean and has not yet been formalized inside Lean.)*

---

## Building and Checking Locally

Requires [Elan](https://github.com/leanprover/elan) (Lean 4 toolchain manager):

```bash
git clone https://github.com/iancenco/relativistic-bounds-lean4.git
cd relativistic-bounds-lean4
lake exe cache get
lake build
```

With the prebuilt Mathlib cache fetched, `lake build` compiles `NaturalMechanics.T4A18_KerrInertia` in ~15–20 seconds.

### Optional Python Scripts

- [`scripts/t4a18_bernstein_certs.py`](scripts/t4a18_bernstein_certs.py) — regenerates the exact rational Bernstein certificates embedded in `T4A18_KerrInertia.lean` (requires `sympy`).
- [`scripts/verify_t4a18_kerr_inertia_floor.py`](scripts/verify_t4a18_kerr_inertia_floor.py) — standalone exact-Sturm / exact-Bernstein Python verification script accompanying the original continuum proof (`python scripts/verify_t4a18_kerr_inertia_floor.py`, requires `sympy`, `numpy`, `scipy`).

---

## Authorship & AI-Assisted Workflow

This repository is authored and maintained by **Serghei Iancenco**. Both the continuum proof development (exact rational Sturm / Bernstein certificate synthesis) and the Lean 4.36.0 formalization were carried out via an **AI-assisted multi-model workflow**:

1. **Proof Development & Exact Certification:** Language models propose and tighten continuum proofs using exact rational algebraic / Bernstein / Sturm certificates rather than floating-point numerics, followed by independent cross-model re-verification.
2. **Lean 4 Formalization:** A formalization pass translates the certified proof chain into zero-`sorry` Lean 4 + Mathlib code.
3. **Cross-Model Statement & Physics Audit:** A separate model reviews the formalized definitions for physics faithfulness, axiom usage, and non-vacuity ([`AUDIT-T4A18.md`](AUDIT-T4A18.md)), catching scope defects (such as the initial omission of interior density jumps) before sign-off.

Logical soundness of the formalized theorems depends strictly on the Lean 4 kernel and the three standard axioms `[propext, Classical.choice, Quot.sound]` (checked on every commit by GitHub Actions). Physical faithfulness of the encoded TOV/Hartle definitions and non-vacuity of the star structures should be judged directly from [`NaturalMechanics/T4A18_KerrInertia.lean`](NaturalMechanics/T4A18_KerrInertia.lean) and [`AUDIT-T4A18.md`](AUDIT-T4A18.md); human physicist review and corrections are warmly welcomed via Issues or PRs.

---

## License

MIT — see [`LICENSE`](LICENSE).
