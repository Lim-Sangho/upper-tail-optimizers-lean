import UpperTailOptimizers.Nondegeneracy.BoundaryExcess

/-!
# Section 6 preliminaries: the log-odds displacement `λ` and the deficit rate `D_d`

This file collects the two scalar quantities introduced at the head of Section 6
(Section 6) of `paper/bipodal_optimizer.tex`, together with the algebraic identity that
drives the whole section.

* `logOdds p = log((1-p)/p)` and the **log-odds displacement**
  `λ(p,r) = log((1-p)/p) - log((1-pc(r))/pc(r))` (`lambdaDisp`).  By strict antitonicity of
  the log-odds, `λ(p,r) > 0` is equivalent to `p < pc(r)` — the symmetry-breaking side.
* `D_d(r,z) = (z^d - r^d)/(d r^{d-1}) - (z - r)` (eq. `Dd-def-main`), positive for `z ≠ r`
  by strict convexity of `u ↦ u^d` (`Dd_pos`).  Twice it is the first-order edge-density
  deficit produced per unit of small-pode mass; it enters `rmk:bipodal-parameter-expansions`.
* The **shift identity** `reducedObjective_sub_Jp_eq_boundaryExcess`:

  `𝓕_{p,r}(r-δ) - J_p(r) = G_r(δ) - λ(p,r)·δ`,

  which converts the one-variable reduction of Section 4 at a general `p` into the boundary
  excess of Section 5 plus a linear term.  This is the display just before
  eq. `scalar-minimization-paper` in the paper; note that the entropy envelope `σ_H` cancels
  entirely, so the identity is pure `log`-algebra and needs no property of `σ_H`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set

/-! ### The log-odds and its displacement `λ(p,r)` -/

/-- The log-odds `log((1-p)/p)` of the background density `p`. -/
noncomputable def logOdds (p : ℝ) : ℝ := Real.log ((1 - p) / p)

/-- On `(0,1)` the log-odds splits as a difference of logarithms. -/
theorem logOdds_eq_sub {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    logOdds p = Real.log (1 - p) - Real.log p :=
  Real.log_div (by linarith : (1:ℝ) - p ≠ 0) (ne_of_gt hp0)

/-- The log-odds is strictly decreasing on `(0,1)`. -/
theorem logOdds_strictAntiOn : StrictAntiOn logOdds (Set.Ioo (0:ℝ) 1) := by
  intro a ha b hb hab
  have hA : (0:ℝ) < (1 - b) / b := div_pos (by linarith [hb.2]) hb.1
  have hlt : (1 - b) / b < (1 - a) / a := by
    rw [div_lt_div_iff₀ hb.1 ha.1]
    nlinarith [ha.1, hb.1, hab]
  exact Real.log_lt_log hA hlt

/-- **The log-odds displacement** `λ(p,r) = log((1-p)/p) - log((1-pc(r))/pc(r))` of Section 6.
It vanishes on the Lubetzky–Zhao boundary `p = pc(r)` and is positive exactly on the
symmetry-breaking side `p < pc(r)`. -/
noncomputable def lambdaDisp {d : ℕ} (M : LZBoundaryArc d) (p r : ℝ) : ℝ :=
  logOdds p - logOdds (M.pc r)

/-- `λ(pc(r), r) = 0`. -/
@[simp] theorem lambdaDisp_self {d : ℕ} (M : LZBoundaryArc d) (r : ℝ) :
    lambdaDisp M (M.pc r) r = 0 := sub_self _

/-- On the symmetry-breaking side `p < pc(r)` the displacement is positive. -/
theorem lambdaDisp_pos {d : ℕ} (M : LZBoundaryArc d) {p r : ℝ} (hr : r ∈ M.U)
    (hp0 : 0 < p) (hp : p < M.pc r) : 0 < lambdaDisp M p r := by
  obtain ⟨hpc0, hpcr, hr1, _⟩ := M.ordering r hr
  have hpc1 : M.pc r < 1 := lt_trans hpcr hr1
  have := logOdds_strictAntiOn ⟨hp0, lt_trans hp hpc1⟩ ⟨hpc0, hpc1⟩ hp
  simpa [lambdaDisp] using sub_pos.mpr this

/-- On the replica-symmetric side `pc(r) ≤ p < 1` the displacement is nonpositive. -/
theorem lambdaDisp_nonpos {d : ℕ} (M : LZBoundaryArc d) {p r : ℝ} (hr : r ∈ M.U)
    (hp : M.pc r ≤ p) (hp1 : p < 1) : lambdaDisp M p r ≤ 0 := by
  obtain ⟨hpc0, hpcr, hr1, _⟩ := M.ordering r hr
  have hpc1 : M.pc r < 1 := lt_trans hpcr hr1
  rcases eq_or_lt_of_le hp with h | h
  · simp [lambdaDisp, ← h]
  · have := logOdds_strictAntiOn ⟨hpc0, hpc1⟩ ⟨lt_trans hpc0 h, hp1⟩ h
    simp only [lambdaDisp]
    linarith

/-! ### The deficit rate `D_d(r,z)` -/

/-- **The first-order edge-density deficit rate** (eq. `Dd-def-main`)
`D_d(r,z) = (z^d - r^d)/(d r^{d-1}) - (z - r)`.  Twice this quantity is the edge-density
deficit produced per unit of small-pode mass, after the large-pode density has been adjusted
to keep the `H`-density fixed. -/
noncomputable def Dd (d : ℕ) (r z : ℝ) : ℝ :=
  (z ^ d - r ^ d) / ((d : ℝ) * r ^ (d - 1)) - (z - r)

/-- `D_d(r,z) = (z^d - r^d - d r^{d-1}(z-r)) / (d r^{d-1})`: the convexity gap, normalised. -/
theorem Dd_eq_gap_div {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) (z : ℝ) :
    Dd d r z = (z ^ d - r ^ d - (d : ℝ) * r ^ (d - 1) * (z - r)) / ((d : ℝ) * r ^ (d - 1)) := by
  have hdR : (0:ℝ) < (d : ℝ) := dpos hd
  have hden : ((d : ℝ) * r ^ (d - 1)) ≠ 0 := ne_of_gt (mul_pos hdR (pow_pos hr _))
  unfold Dd
  field_simp

/-- **Positivity of the deficit rate** (`Strict convexity of u ↦ u^d gives D_d(r,z) > 0`). -/
theorem Dd_pos {d : ℕ} (hd : 2 ≤ d) {r z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) (hne : z ≠ r) :
    0 < Dd d r z := by
  have hdR : (0:ℝ) < (d : ℝ) := dpos hd
  have hden : (0:ℝ) < (d : ℝ) * r ^ (d - 1) := mul_pos hdR (pow_pos hr _)
  rw [Dd_eq_gap_div hd hr]
  exact div_pos (pow_convex_gap_pos hr hz hne hd) hden

/-! ### The shift identity -/

/-- The reduced objective minus the constant-graphon value, with the `p`-dependence isolated:

`𝓕_{p,r}(ε) - J_p(r) = -2 σ_H(ε,τ) - [r log r + (1-r) log(1-r)] + (ε - r)·log((1-p)/p)`.

Only the last term depends on `p`. -/
theorem reducedObjective_sub_Jp {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {p ε τ r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    reducedObjective H p ε τ - Jp p r
      = -2 * entropyEnvelope H ε τ - entIntegrand r + (ε - r) * logOdds p := by
  have hlog : Real.log ((1 - p) / p) = Real.log (1 - p) - Real.log p :=
    Real.log_div (by linarith : (1:ℝ) - p ≠ 0) (ne_of_gt hp0)
  rw [reducedObjective, logOdds, hlog, Jp_eq_entIntegrand hp0 hp1 hr0 hr1]
  ring

/-- **The shift identity of Section 6.**  For every `p ∈ (0,1)` and every edge-density deficit
`δ`,

`𝓕_{p,r}(r-δ) - J_p(r) = G_r(δ) - λ(p,r)·δ`,

where `G_r` is the boundary excess of Section 5 and `λ(p,r)` the log-odds displacement.  This
is the display preceding eq. `scalar-minimization-paper`: changing `p` away from the boundary
value `pc(r)` tilts the reduced objective by exactly the linear function `-λ(p,r)·δ`.  The
entropy envelope cancels, so no property of `σ_H` is used. -/
theorem reducedObjective_sub_Jp_eq_boundaryExcess {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (M : LZBoundaryArc d) {p r δ : ℝ}
    (hr : r ∈ M.U) (hp0 : 0 < p) (hp1 : p < 1) :
    reducedObjective H p (r - δ) (r ^ H.edgeFinset.card) - Jp p r
      = boundaryExcess H M r δ - lambdaDisp M p r * δ := by
  obtain ⟨hpc0, hpcr, hr1, _⟩ := M.ordering r hr
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  have hpc1 : M.pc r < 1 := lt_trans hpcr hr1
  rw [boundaryExcess,
    reducedObjective_sub_Jp H hp0 hp1 hr0.le hr1.le,
    reducedObjective_sub_Jp H hpc0 hpc1 hr0.le hr1.le, lambdaDisp]
  ring

end UpperTailOptimizers
