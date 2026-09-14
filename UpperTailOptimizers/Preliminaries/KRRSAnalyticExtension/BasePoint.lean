import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Stationarity
import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.PsiExists

/-!
# The degenerate first-pode density `a_d(ε)`, without Kenyon–Radin–Ren–Sadun

At `c = 0` the first desingularized stationarity equation is affine in `S₀'(a)`:

  `F₁(ε,a,b,0) = (S₀'(a) - S₀'(ε))·𝒜(ε,b) - 𝒩_ε(b)·Rda(ε,·,b,0)`,

where `Rda(ε,·,b,0)` does not depend on `a` (`Rda_zero_indep_a`) and `𝒜(ε,b) > 0` off the
diagonal.  Since `S₀'` is a bijection `(0,1) → ℝ` with the logistic inverse, the equation has
exactly one solution, `baseA`.  It is the base point of the analytic family of
`Preliminaries/KRRSAnalyticExtension/FamilyCore.lean`.

## Contents

* `logistic`, `dS0_logistic`, `logistic_dS0` — the inverse of `S₀'`;
* `F1_zero_eq` — the affine form of `F₁` at `c = 0`;
* `baseA`, `baseA_mem`, `F1_baseA`, `eq_baseA_of_F1` — existence and uniqueness.
-/

namespace UpperTailOptimizers

open Real

/-- The inverse of `S₀'(u) = ½ log((1-u)/u)`. -/
noncomputable def logistic (y : ℝ) : ℝ := 1 / (1 + Real.exp (2 * y))

theorem logistic_mem (y : ℝ) : logistic y ∈ Set.Ioo (0:ℝ) 1 := by
  unfold logistic
  have h : 0 < Real.exp (2 * y) := Real.exp_pos _
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

theorem dS0_logistic (y : ℝ) : dS0 (logistic y) = y := by
  unfold dS0 logistic
  have h : 0 < Real.exp (2 * y) := Real.exp_pos _
  have h1 : (1:ℝ) - 1 / (1 + Real.exp (2 * y)) = Real.exp (2 * y) / (1 + Real.exp (2 * y)) := by
    field_simp; ring
  rw [h1, Real.log_div (ne_of_gt h) (by positivity), Real.log_div one_ne_zero (by positivity),
    Real.log_exp, Real.log_one]
  ring

theorem logistic_dS0 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : logistic (dS0 a) = a := by
  unfold logistic dS0
  have h1a : (0:ℝ) < 1 - a := by linarith
  have hexp : Real.exp (2 * ((Real.log (1 - a) - Real.log a) / 2)) = (1 - a) / a := by
    rw [show 2 * ((Real.log (1 - a) - Real.log a) / 2) = Real.log (1 - a) - Real.log a by ring,
      Real.exp_sub, Real.exp_log h1a, Real.exp_log ha0]
  rw [hexp]
  field_simp
  ring

/-- **`F₁` at `c = 0` is affine in `S₀'(a)`.** -/
theorem F1_zero_eq {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    F1 H d ε a b 0 = (dS0 a - dS0 ε) * Afun H d ε b - Nfun ε b * Rda H d ε a b 0 := by
  unfold F1
  rw [Qmap_zero, partialC_That_zero H hd hreg hm ε a b,
    partialC_Shat_zero hε0 hε1 ha0 ha1 hb0 hb1]

/-- The unique solution `a` of `F₁(ε,a,b,0) = 0`: the paper's `a_d(ε)` at `b = ζ_d(ε)`. -/
noncomputable def baseA {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε b : ℝ) : ℝ :=
  logistic (dS0 ε + Nfun ε b * Rda H d ε (1 / 2) b 0 / Afun H d ε b)

theorem baseA_mem {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε b : ℝ) : baseA H d ε b ∈ Set.Ioo (0:ℝ) 1 :=
  logistic_mem _

theorem F1_baseA {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hb0 : 0 < b) (hb1 : b < 1) (hbε : b ≠ ε) :
    F1 H d ε (baseA H d ε b) b 0 = 0 := by
  obtain ⟨ha0, ha1⟩ := baseA_mem H d ε b
  have hA : Afun H d ε b ≠ 0 := ne_of_gt (Afun_pos H hd (by omega) hε0 hb0.le hbε)
  rw [F1_zero_eq H hd hreg hm hε0 hε1 ha0 ha1 hb0 hb1, baseA, dS0_logistic,
    Rda_zero_indep_a H d ε b (logistic _) (1 / 2)]
  field_simp
  ring

theorem eq_baseA_of_F1 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) (hbε : b ≠ ε)
    (hF : F1 H d ε a b 0 = 0) : a = baseA H d ε b := by
  have hA : Afun H d ε b ≠ 0 := ne_of_gt (Afun_pos H hd (by omega) hε0 hb0.le hbε)
  rw [F1_zero_eq H hd hreg hm hε0 hε1 ha0 ha1 hb0 hb1,
    Rda_zero_indep_a H d ε b a (1 / 2)] at hF
  have hkey : dS0 a = dS0 ε + Nfun ε b * Rda H d ε (1 / 2) b 0 / Afun H d ε b := by
    field_simp
    linarith
  rw [← logistic_dS0 ha0 ha1, hkey]
  rfl

end UpperTailOptimizers
