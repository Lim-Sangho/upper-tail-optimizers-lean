import UpperTailOptimizers.LZBoundary.Phi
import UpperTailOptimizers.LZBoundary.PhiConvex

/-!
# Oriented Lubetzky–Zhao boundary arcs (the Lean packaging of `thm:scalar-lz-boundary`)

This file introduces the `LZBoundaryArc` record.  `paper/bipodal_optimizer.tex` has no corresponding
definition: its `thm:scalar-lz-boundary` (Section 3 `sec:lz-boundary`) states
conditions (M1)–(M5) directly about the global analytic maps `pc`, `sm`.  The record is a
Lean-side abstraction that bundles those conditions on an interval `U`, plus one extra
window condition the development needs (`noFlatTie`); `scalar_lz_boundary_arcs`
(`LZBoundary/Existence.lean`) is the Lean form of `thm:scalar-lz-boundary` and constructs such an arc
through every non-exceptional `r₀`.

We work in the `u`-coordinate `u = x^{1/d}` (so `x = u^d`); the Lubetzky–Zhao one-variable
graph is `x ↦ J_p(x^{1/d})`, and at the contact `x = r^d` the supporting line has slope
`φ'_{p}(r^d) = J_p'(r)/(d r^{d-1})`, recorded as `slope`.

**Field-to-paper dictionary.**  The correspondence with `thm:scalar-lz-boundary` is not a bijection, so
each field docstring names its counterpart explicitly:

| field           | `thm:scalar-lz-boundary`                                                       |
|-----------------|-------------------------------------------------------------------|
| `ordering`      | part of (M1) (`0 < pc(r) < r < 1`, `sm(r) ≠ r`, `sm(r) ∈ (0,1)`)   |
| `pcLtPStar`     | the `pc(r) < p_*` half of (M1)                                    |
| `supporting`    | (M3) (the tangent line `ℓ_r` lies below the graph)                |
| `secondContact` | the `⊇` half of (M4) (the contact set contains `sm(r)^d`)         |
| `quadSep`       | (M5) (uniform quadratic separation, equation `eq:contact-quadratic-separation`)                 |
| `orientation`   | the `p ≥ pc(r)` half of (M2), on the window `(pc r, p_*)`         |
| `brokenSide`    | the `p < pc(r)` half of (M2)                                      |
| `noFlatTie`     | no counterpart — a Lean-side window condition                     |

Both halves of (M2) are stated on their *global* windows — `(0, pc r)` and `(pc r, p_*)` —
rather than on unspecified one-sided neighbourhoods, so that they are automatically uniform
over compact subarcs.  An arc is `NonExceptional` at `r` when `r ≠ (d-1)/d`.
`boundary_uniqueness` consumes `ordering`, `supporting` and `quadSep`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real

/-- The supporting-line slope `φ'_{p}(r^d) = J_p'(r)/(d r^{d-1})` at the contact
`x = r^d`. -/
noncomputable def slope (d : ℕ) (pc : ℝ → ℝ) (r : ℝ) : ℝ :=
  Jp' (pc r) r / ((d : ℝ) * r ^ (d - 1))

/-- Positivity of the supporting-line slope, from `pc(r) < r` (used by
`boundary_uniqueness`). -/
theorem slope_pos {d : ℕ} (hd : 1 ≤ d) {pc : ℝ → ℝ} {r : ℝ}
    (hpc0 : 0 < pc r) (hpcr : pc r < r) (hr1 : r < 1) : 0 < slope d pc r := by
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  have hdR : (0:ℝ) < d := by
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hden : 0 < (d : ℝ) * r ^ (d - 1) := mul_pos hdR (pow_pos hr0 _)
  have harg : 1 < r * (1 - pc r) / ((1 - r) * pc r) := by
    rw [lt_div_iff₀ (mul_pos (by linarith) hpc0)]
    nlinarith [hpcr]
  have hlog : 0 < Jp' (pc r) r := by
    unfold Jp'; exact Real.log_pos harg
  exact div_pos hlog hden

/-- An **oriented Lubetzky–Zhao boundary arc** for the degree-`d` problem.  A Lean-side record with
no numbered counterpart in `paper/bipodal_optimizer.tex`.  `U` is the arc, `pc` the boundary curve
`p = pc(r)`, `sm` the second-contact density `s(r)`.  The condition labels below are those
of `thm:scalar-lz-boundary` of `paper/bipodal_optimizer.tex`; see the module docstring for the dictionary. -/
structure LZBoundaryArc (d : ℕ) where
  /-- The interval of target densities `r`. -/
  U : Set ℝ
  isOpen_U : IsOpen U
  /-- The Lubetzky–Zhao boundary curve `p = pc(r)`. -/
  pc : ℝ → ℝ
  /-- The second-contact density `s(r)`. -/
  sm : ℝ → ℝ
  /-- `pc` is real-analytic on `U`. -/
  analytic_pc : AnalyticOnNhd ℝ pc U
  /-- `sm` is real-analytic on `U`. -/
  analytic_sm : AnalyticOnNhd ℝ sm U
  /-- Part of (M1) of `thm:scalar-lz-boundary`: `0 < pc(r) < r < 1` and `sm(r) ≠ r`, with
  `sm(r) ∈ (0,1)`. -/
  ordering : ∀ r ∈ U, 0 < pc r ∧ pc r < r ∧ r < 1 ∧ sm r ≠ r ∧ 0 < sm r ∧ sm r < 1
  /-- (M3): the tangent line `ℓ_r` at `r^d` lies below the graph (supporting line). -/
  supporting : ∀ r ∈ U, ∀ u ∈ Set.Icc (0:ℝ) 1,
    Jp (pc r) r + slope d pc r * (u ^ d - r ^ d) ≤ Jp (pc r) u
  /-- Half of (M4): a second contact at `sm(r)^d`.  (The full (M4) — that the contact set
  is exactly `{r^d, sm(r)^d}` — is derived in `LZBoundary/Curve.lean` from this together with
  `quadSep`.) -/
  secondContact : ∀ r ∈ U,
    Jp (pc r) (sm r) = Jp (pc r) r + slope d pc r * ((sm r) ^ d - r ^ d)
  /-- (M5): uniform quadratic separation on compact subarcs (equation `eq:contact-quadratic-separation`,
  `eq:contact-quadratic-separation`). -/
  quadSep : ∀ K ⊆ U, IsCompact K → ∃ γ : ℝ, 0 < γ ∧ ∀ r ∈ K, ∀ u ∈ Set.Icc (0:ℝ) 1,
    γ * (min |u ^ d - r ^ d| |u ^ d - (sm r) ^ d|) ^ 2
      ≤ Jp (pc r) u - (Jp (pc r) r + slope d pc r * (u ^ d - r ^ d))
  /-- The remaining half of (M1): `pc(r) < p_*`, i.e. the boundary curve stays below the
  threshold probability above which `φ_{p,d}` is convex.  This is what makes the
  replica-symmetric window `(pc r, p_*)` of `orientation`/`noFlatTie` non-empty. -/
  pcLtPStar : ∀ r ∈ U, pc r < pStar d
  /-- The replica-symmetric half of (M2): for every `p` with `pc(r) < p < p_*`
  a supporting line of `φ_{p,d}` at `x = r^d` persists.  (The broken side is the
  global field `brokenSide` below.)  Stating the window as `(pc r, p_*)` rather than
  as an unspecified `(pc r, pc r + δ)` is what makes the window uniform over compact
  subarcs, since `pc` is continuous and `pc < p_*` on the arc. -/
  orientation : ∀ r ∈ U, ∀ p, pc r < p → p < pStar d →
    ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x
  /-- **No flat tie** — a Lean-side window condition with no counterpart in `thm:scalar-lz-boundary`.
  On the replica-symmetric side (Jensen form): for `pc(r) < p < p_*`, any `[0,1]`-valued
  law `μ` with mean `r^d` has `∫ φ_{p,d} dμ ≥ J_p(r)`, with equality only at the Dirac
  mass at `r^d`. -/
  noFlatTie : ∀ r ∈ U, ∀ p, pc r < p → p < pStar d →
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc (0:ℝ) 1)ᶜ = 0 →
      (∫ x, x ∂μ = r ^ d) →
        Jp p r ≤ ∫ x, phi p d x ∂μ ∧
          (∫ x, phi p d x ∂μ = Jp p r → μ = Measure.dirac (r ^ d))
  /-- The symmetry-breaking half of (M2): for every `0 < p < pc(r)` the point `r^d` is not
  on the convex minorant of `φ_{p,d}`, i.e. no supporting affine line touches `φ_{p,d}` at
  `x = r^d`.  The `orientation` field above is the `p ≥ pc(r)` half of the same
  condition. -/
  brokenSide : ∀ r ∈ U, ∀ p, 0 < p → p < pc r →
    ¬ ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x

/-- A point `r ∈ U` is non-exceptional when `r ≠ (d-1)/d`. -/
def LZBoundaryArc.NonExceptional {d : ℕ} (_M : LZBoundaryArc d) (r : ℝ) : Prop := r ≠ rStar d

end UpperTailOptimizers
