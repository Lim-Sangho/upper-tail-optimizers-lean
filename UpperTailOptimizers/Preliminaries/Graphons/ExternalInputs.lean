import UpperTailOptimizers.Preliminaries.Graphons.Bipodal
import UpperTailOptimizers.LZBoundary.Phi
import UpperTailOptimizers.Preliminaries.Graphons.RegularGraph

/-!
# External inputs (Sections 1–2) and the generalized Hölder inequality

This file records the external results of Sections 1–2 of `paper/paper.tex` that are
taken **as axioms**:

* `lubetzkyZhao`      — `thm:lz-criterion` (the Lubetzky–Zhao
  replica-symmetry criterion),
* `generalized_holder` — the generalized Hölder inequality, equation `eq:generalized-holder`,

together with the moment-bound consequence `holder_moment`, which **is** proved here and is
used by `boundary_uniqueness`.  (The Chatterjee–Varadhan graphon LDP, `thm:graphon-large-deviations`, is
neither assumed nor used anywhere in the formalisation; see the prose in
`Preliminaries/Graphons/CutMetric.lean`.)

`lubetzkyZhao` is stated in the supporting-line form, equivalent to the
convex-minorant condition: the point `(r^d, J_p(r))` lies on the convex minorant
of `x ↦ J_p(x^{1/d})` iff there is a supporting affine function touching the
graph at `x = r^d`.

**`thm:krrs-analytic-extension` (Kenyon–Radin–Ren–Sadun)** used to live here, as the two
monolithic axioms `kenyonRadinRenSadun` and `kenyonRadinRenSadunAnalytic`.  Both are now
**theorems**, proved in `UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/Main.lean` following Appendix B of
`paper/paper.tex`.  Neither Kenyon–Radin–Ren–Sadun statement it uses is assumed:
their Theorem 3.3 is `krrs_thm33` (`UpperTailOptimizers/Preliminaries/KRRSAnalyticExtension/Inputs.lean`), and their
Theorem 1.1 is proved for `d`-regular graphs in `UpperTailOptimizers/Preliminaries/KRRSBipodality/`, from
`generalized_holder` and the four cut axioms of `Preliminaries/Graphons/CutContinuity.lean`.  They cannot be stated here:
their proofs need the two-block graphon
layer of `Preliminaries/Graphons/BipodalBridge.lean` and `NonexceptionalEndpoint/QuadraticGrowth/TDensityExpansion.lean`,
both of which are downstream of this file.
-/

namespace UpperTailOptimizers

open MeasureTheory Real

/-- The constant graphon `W ≡ r`. -/
noncomputable def constGraphon (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) : Graphon where
  toFun := fun _ _ => r
  symm' := by intro x y; rfl
  meas' := by fun_prop
  nonneg' := by intro x y; exact hr.1
  le_one' := by intro x y; exact hr.2

@[simp] theorem constGraphon_apply (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) (x y : ℝ) :
    (constGraphon r hr).toFun x y = r := rfl

namespace Graphon

/-- The `d`-th moment of a graphon is nonnegative. -/
theorem Wmoment_nonneg (W : Graphon) (d : ℕ) : 0 ≤ W.Wmoment d := by
  unfold Graphon.Wmoment
  exact integral_nonneg (fun z => pow_nonneg (W.nonneg' z.1 z.2) d)

end Graphon

/-! ### The generalized Hölder inequality (equation `eq:generalized-holder`). -/

/-- The generalized Hölder inequality, equation `eq:generalized-holder`: for a `d`-regular
graph `H` with `m` edges, `t(H,W) ≤ (∫ W^d)^{m/d}`.  Taken as an axiom (part of
the Lubetzky–Zhao toolkit).

As for `lubetzkyZhao`, the paper's standing
hypotheses `2 ≤ d` and `1 ≤ |E(H)|` are carried explicitly. These restrict the axiom to
the range used in the paper. The consequence `holder_moment` has the same hypotheses. -/
axiom generalized_holder {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) (W : Graphon) :
    W.tDensity H ≤ Real.rpow (W.Wmoment d) ((H.edgeFinset.card : ℝ) / (d : ℝ))

/-- Moment consequence of generalized Hölder, used by `boundary_uniqueness`: if `t(H,W) ≥ r^m`
then the `d`-th moment satisfies `∫ W^d ≥ r^d`. -/
theorem holder_moment {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d)
    (hd : 2 ≤ d) (W : Graphon) {r : ℝ} (hr0 : 0 ≤ r) (hm : 1 ≤ H.edgeFinset.card)
    (hcon : r ^ (H.edgeFinset.card) ≤ W.tDensity H) :
    r ^ d ≤ W.Wmoment d := by
  set m := H.edgeFinset.card with hm_def
  set M := W.Wmoment d with hM_def
  have hM0 : 0 ≤ M := W.Wmoment_nonneg d
  have hdR : (0:ℝ) < d := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hd
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have h2 : W.tDensity H ≤ M ^ ((m:ℝ) / (d:ℝ)) := generalized_holder H hd hreg hm W
  have h1 : (r:ℝ) ^ ((m:ℝ)) ≤ M ^ ((m:ℝ) / (d:ℝ)) := by
    rw [Real.rpow_natCast]; exact le_trans hcon h2
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg hr0 (m:ℝ)) h1
    (by positivity : (0:ℝ) ≤ (d:ℝ) / (m:ℝ))
  have hL : (r ^ ((m:ℝ))) ^ ((d:ℝ) / (m:ℝ)) = r ^ d := by
    rw [← Real.rpow_mul hr0, show (m:ℝ) * ((d:ℝ) / (m:ℝ)) = (d:ℝ) by field_simp,
      Real.rpow_natCast]
  have hR : (M ^ ((m:ℝ) / (d:ℝ))) ^ ((d:ℝ) / (m:ℝ)) = M := by
    rw [← Real.rpow_mul hM0, show (m:ℝ) / (d:ℝ) * ((d:ℝ) / (m:ℝ)) = 1 by field_simp,
      Real.rpow_one]
  rw [hL, hR] at hraise
  exact hraise

/-! ### The upper-tail variational value and the Lubetzky–Zhao criterion. -/

/-- Feasibility for the upper-tail problem: `t(H,W) ≥ r^{e(H)}`. -/
def Feasible {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (r : ℝ) (W : Graphon) : Prop := r ^ (H.edgeFinset.card) ≤ W.tDensity H

/-- The upper-tail variational value `Φ_H(p,r) = inf { I_p(W) : t(H,W) ≥ r^m }`. -/
noncomputable def phiVar {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p r : ℝ) : ℝ :=
  sInf {y | ∃ W : Graphon, Feasible H r W ∧ W.Ip p = y}

/-- **`thm:lz-criterion`**, as an axiom. For a `d`-regular `H` and
`0 < p < r < 1`, the variational value equals `J_p(r)` iff `(r^d, J_p(r))` lies on
the convex minorant of `x ↦ J_p(x^{1/d})`; the latter is expressed in
supporting-line form.

The paper's standing
assumptions `2 ≤ d` and `1 ≤ |E(H)|` are carried explicitly: without them the statement is
*refutable inside Lean*.  Instantiating at an empty vertex type with `d = 0` makes every
graphon feasible (the empty product gives `t(H,W) = 1 = r^0`), so `Φ_H(p,r) = 0 ≠ J_p(r)`,
while the right-hand side holds with slope `a = 0` because `phi p 0 ≡ J_p(1) > J_p(r)`. -/
axiom lubetzkyZhao {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1) :
    phiVar H p r = Jp p r ↔
      ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1,
        Jp p r + a * (x - r ^ d) ≤ phi p d x

end UpperTailOptimizers
