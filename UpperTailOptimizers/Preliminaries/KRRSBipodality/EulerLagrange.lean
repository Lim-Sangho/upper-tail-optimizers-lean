import UpperTailOptimizers.Preliminaries.KRRSBipodality.Correction

/-!
# The Euler–Lagrange equation for fixed-density entropy maximizers

Let `W` maximize `s` on `{e = e₀, t(H,·) = t₀}`.  Given two *qualifying directions* `χ₁, χ₂`
(bounded, symmetric, supported where `W ∈ [η, 1-η]`, with nonzero determinant
`D = (∬χ₁)(∬χ₂Γ_W) - (∬χ₂)(∬χ₁Γ_W)`), define the multipliers `(α, β)` by
`α ∬χ_k + β ∬χ_k Γ_W = ∬ S₀'(W) χ_k`.  Then (draft `kb:lem:el`)

* `∬ S₀'(W) φ = α ∬ φ + β ∬ φ Γ_W` for every bounded symmetric `φ` supported away from `{0,1}`;
* `S₀'(W) = α + β Γ_W` almost everywhere on `{0 < W < 1}`;
* `W ∉ {0, 1}` almost everywhere.

## Contents

* `IsMaximizer`, `QualDirs`, `QualDirs.alpha`, `QualDirs.beta`;
* `QualDirs.el_linear` — the weak Euler–Lagrange identity.
-/

namespace UpperTailOptimizers

open MeasureTheory Set

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- `W` maximizes the entropy on `{e = e₀, t(H,·) = t₀}`. -/
def IsMaximizer (W : Graphon) (e₀ t₀ : ℝ) : Prop :=
  W.edgeDensity = e₀ ∧ W.tDensity H = t₀ ∧
    ∀ W' : Graphon, W'.edgeDensity = e₀ → W'.tDensity H = t₀ → W'.entropy ≤ W.entropy

/-- **Qualifying directions** for a graphon `W`: two bounded symmetric measurable kernels
supported where `W ∈ [η, 1-η]`, with nonzero constraint determinant. -/
structure QualDirs (W : Graphon) where
  η : ℝ
  η_pos : 0 < η
  η_le : η ≤ 1 / 2
  χ₁ : ℝ → ℝ → ℝ
  χ₂ : ℝ → ℝ → ℝ
  meas₁ : Measurable fun p : ℝ × ℝ => χ₁ p.1 p.2
  meas₂ : Measurable fun p : ℝ × ℝ => χ₂ p.1 p.2
  symm₁ : ∀ x y, χ₁ x y = χ₁ y x
  symm₂ : ∀ x y, χ₂ x y = χ₂ y x
  bound₁ : ∀ x y, |χ₁ x y| ≤ 1
  bound₂ : ∀ x y, |χ₂ x y| ≤ 1
  supp : ∀ x y, χ₁ x y ≠ 0 ∨ χ₂ x y ≠ 0 → W.toFun x y ∈ Icc η (1 - η)
  det_ne : (∫ p : ℝ × ℝ, χ₁ p.1 p.2 ∂gμ) * (∫ p : ℝ × ℝ, χ₂ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ)
      - (∫ p : ℝ × ℝ, χ₂ p.1 p.2 ∂gμ) * (∫ p : ℝ × ℝ, χ₁ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ) ≠ 0

namespace QualDirs

variable {H} {W : Graphon} (Q : QualDirs H W)

noncomputable def c₁ : ℝ := ∫ p : ℝ × ℝ, Q.χ₁ p.1 p.2 ∂gμ
noncomputable def c₂ : ℝ := ∫ p : ℝ × ℝ, Q.χ₂ p.1 p.2 ∂gμ
noncomputable def g₁ : ℝ := ∫ p : ℝ × ℝ, Q.χ₁ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ
noncomputable def g₂ : ℝ := ∫ p : ℝ × ℝ, Q.χ₂ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ
noncomputable def s₁ : ℝ := ∫ p : ℝ × ℝ, dS0 (W.toFun p.1 p.2) * Q.χ₁ p.1 p.2 ∂gμ
noncomputable def s₂ : ℝ := ∫ p : ℝ × ℝ, dS0 (W.toFun p.1 p.2) * Q.χ₂ p.1 p.2 ∂gμ
noncomputable def det : ℝ := Q.c₁ * Q.g₂ - Q.c₂ * Q.g₁

/-- The multiplier of the edge constraint. -/
noncomputable def alpha : ℝ := (Q.s₁ * Q.g₂ - Q.s₂ * Q.g₁) / Q.det

/-- The multiplier of the `H`-density constraint. -/
noncomputable def beta : ℝ := (Q.c₁ * Q.s₂ - Q.c₂ * Q.s₁) / Q.det

theorem det_ne_zero : Q.det ≠ 0 := Q.det_ne

theorem alpha_beta_eq₁ : Q.alpha * Q.c₁ + Q.beta * Q.g₁ = Q.s₁ := by
  unfold alpha beta
  field_simp [Q.det_ne_zero]
  unfold det
  ring

theorem alpha_beta_eq₂ : Q.alpha * Q.c₂ + Q.beta * Q.g₂ = Q.s₂ := by
  unfold alpha beta
  field_simp [Q.det_ne_zero]
  unfold det
  ring

end QualDirs

/-! ### Small linear-algebra and integration facts -/

/-- If `h L ≤ C h²` for all `|h| ≤ h₀`, then `L = 0`. -/
theorem eq_zero_of_mul_le_sq {L C h₀ : ℝ} (hh₀ : 0 < h₀) (hC : 0 ≤ C)
    (hle : ∀ h : ℝ, |h| ≤ h₀ → h * L ≤ C * h ^ 2) : L = 0 := by
  by_contra hL
  set h₁ : ℝ := min h₀ (|L| / (2 * (C + 1))) with hh₁
  have hh₁pos : 0 < h₁ := lt_min hh₀ (by positivity)
  have hh₁le : h₁ ≤ |L| / (2 * (C + 1)) := min_le_right _ _
  have hsmall : C * h₁ < |L| := by
    have h1 : C * h₁ ≤ C * (|L| / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hh₁le hC
    have h2 : C * (|L| / (2 * (C + 1))) < |L| := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      have : 0 < |L| := abs_pos.mpr hL
      nlinarith
    linarith
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · have h := hle (-h₁) (by rw [abs_neg, abs_of_pos hh₁pos]; exact min_le_left _ _)
    have : h₁ * |L| ≤ C * h₁ ^ 2 := by
      rw [abs_of_neg hneg]; nlinarith
    have : |L| ≤ C * h₁ := by
      have := (mul_le_mul_iff_right₀ hh₁pos).mp (by nlinarith : h₁ * |L| ≤ h₁ * (C * h₁))
      exact this
    linarith
  · have h := hle h₁ (by rw [abs_of_pos hh₁pos]; exact min_le_left _ _)
    have : |L| ≤ C * h₁ := by
      rw [abs_of_pos hpos]
      exact (mul_le_mul_iff_right₀ hh₁pos).mp (by nlinarith : h₁ * L ≤ h₁ * (C * h₁))
    linarith

theorem integral_abs_mul_le_of_bound {f g : ℝ × ℝ → ℝ} {A B : ℝ} (hfb : ∀ p, |f p| ≤ A) (hgb : ∀ p, |g p| ≤ B) :
    |∫ p, f p * g p ∂gμ| ≤ A * B := by
  have hA : 0 ≤ A := le_trans (abs_nonneg _) (hfb (0, 0))
  have h := norm_integral_le_of_norm_le_const (μ := gμ) (f := fun p => f p * g p)
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hfb p) (hgb p) (abs_nonneg _) hA)
  simpa [Real.norm_eq_abs, measureReal_def, gμ] using h

theorem integral_lin_three {f₁ f₂ f₃ : ℝ × ℝ → ℝ} (h₁ : Integrable f₁ gμ) (h₂ : Integrable f₂ gμ)
    (h₃ : Integrable f₃ gμ) (a b c : ℝ) :
    ∫ p, (a * f₁ p + b * f₂ p + c * f₃ p) ∂gμ
      = a * ∫ p, f₁ p ∂gμ + b * ∫ p, f₂ p ∂gμ + c * ∫ p, f₃ p ∂gμ := by
  rw [integral_add (f := fun p => a * f₁ p + b * f₂ p) (g := fun p => c * f₃ p)
      ((h₁.const_mul a).add (h₂.const_mul b)) (h₃.const_mul c),
    integral_add (f := fun p => a * f₁ p) (g := fun p => b * f₂ p) (h₁.const_mul a)
      (h₂.const_mul b), integral_const_mul, integral_const_mul, integral_const_mul]

theorem integrable_bdd_mul_gammaW (W : Graphon) {χ : ℝ → ℝ → ℝ}
    (hm : Measurable fun p : ℝ × ℝ => χ p.1 p.2) {C : ℝ} (hb : ∀ x y, |χ x y| ≤ C) :
    Integrable (fun p : ℝ × ℝ => χ p.1 p.2 * W.gammaW H p.1 p.2) gμ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0 0)
  refine integrable_of_abs_le (hm.mul (W.measurable_gammaW H)) (C * H.edgeFinset.card) fun p => ?_
  rw [abs_mul, abs_of_nonneg (W.gammaW_nonneg H _ _)]
  exact mul_le_mul (hb _ _) (W.gammaW_le H _ _) (W.gammaW_nonneg H _ _) hC

theorem abs_dS0_mul_le (W : Graphon) {χ : ℝ → ℝ → ℝ} {C : ℝ} (hb : ∀ x y, |χ x y| ≤ C)
    {η L : ℝ} (hL : ∀ w ∈ Icc η (1 - η), |dS0 w| ≤ L)
    (hsupp : ∀ x y, χ x y ≠ 0 → W.toFun x y ∈ Icc η (1 - η)) (x y : ℝ) :
    |dS0 (W.toFun x y) * χ x y| ≤ max L 0 * C := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0 0)
  by_cases h0 : χ x y = 0
  · rw [h0, mul_zero, abs_zero]; exact mul_nonneg (le_max_right _ _) hC
  · rw [abs_mul]
    exact mul_le_mul (le_trans (hL _ (hsupp x y h0)) (le_max_left _ _)) (hb x y) (abs_nonneg _)
      (le_max_right _ _)

theorem integrable_dS0_mul (W : Graphon) {χ : ℝ → ℝ → ℝ}
    (hm : Measurable fun p : ℝ × ℝ => χ p.1 p.2) {C : ℝ} (hb : ∀ x y, |χ x y| ≤ C) {η : ℝ}
    (hη : 0 < η) (hsupp : ∀ x y, χ x y ≠ 0 → W.toFun x y ∈ Icc η (1 - η)) :
    Integrable (fun p : ℝ × ℝ => dS0 (W.toFun p.1 p.2) * χ p.1 p.2) gμ := by
  obtain ⟨L, hL⟩ := exists_abs_dS0_le hη
  exact integrable_of_abs_le ((measurable_dS0.comp W.measurable_uncurry).mul hm) (max L 0 * C)
    fun p => abs_dS0_mul_le W hb hL hsupp p.1 p.2

set_option maxHeartbeats 4000000 in
/-- **The weak Euler–Lagrange identity** (draft `kb:lem:el`): for a maximizer with qualifying
directions, `∬ S₀'(W) φ = α ∬ φ + β ∬ φ Γ_W` for every bounded symmetric `φ` supported where
`W ∈ [η', 1-η']`. -/
theorem QualDirs.el_linear {W : Graphon} {e₀ t₀ : ℝ} (hmax : IsMaximizer H W e₀ t₀)
    (Q : QualDirs H W) {φ : ℝ → ℝ → ℝ} (hφm : Measurable fun p : ℝ × ℝ => φ p.1 p.2)
    (hφs : ∀ x y, φ x y = φ y x) (hφb : ∀ x y, |φ x y| ≤ 1) {η' : ℝ} (hη' : 0 < η')
    (hη'1 : η' ≤ 1 / 2) (hφsupp : ∀ x y, φ x y ≠ 0 → W.toFun x y ∈ Icc η' (1 - η')) :
    ∫ p : ℝ × ℝ, dS0 (W.toFun p.1 p.2) * φ p.1 p.2 ∂gμ
      = Q.alpha * ∫ p : ℝ × ℝ, φ p.1 p.2 ∂gμ
        + Q.beta * ∫ p : ℝ × ℝ, φ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ := by
  classical
  obtain ⟨he, ht, hopt⟩ := hmax
  set mR : ℝ := (H.edgeFinset.card : ℝ) with hmR
  have hmR0 : 0 ≤ mR := Nat.cast_nonneg _
  set M : ℝ := (2:ℝ) ^ H.edgeFinset.card with hM
  have hM0 : 0 < M := by positivity
  set η₀ : ℝ := min Q.η η' with hη₀
  have hη₀pos : 0 < η₀ := lt_min Q.η_pos hη'
  have hη₀le : η₀ ≤ 1 / 2 := le_trans (min_le_left _ _) Q.η_le
  have hdetpos : 0 < |Q.det| := abs_pos.mpr Q.det_ne_zero
  obtain ⟨ρ₀, K, hρ₀, hK, hcorr⟩ := exists_correction H (η := Q.η / 2) (D₀ := |Q.det| / 2)
    (by linarith [Q.η_pos]) (by linarith [Q.η_le]) (by linarith)
  set Lφ : ℝ := ∫ p : ℝ × ℝ, φ p.1 p.2 ∂gμ with hLφ
  set Gφ : ℝ := ∫ p : ℝ × ℝ, φ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ with hGφ
  set Sφ : ℝ := ∫ p : ℝ × ℝ, dS0 (W.toFun p.1 p.2) * φ p.1 p.2 ∂gμ with hSφ
  set Cρ : ℝ := 1 + mR + M with hCρ
  have hCρ0 : 0 < Cρ := by positivity
  set C₁ : ℝ := 1 + K * Cρ with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  set h₀ : ℝ := min (min (η' / 2) (Q.η / 2))
    (min (|Q.det| / (4 * mR ^ 2 + 1)) (min (ρ₀ / Cρ) (min 1 (η₀ / (2 * C₁))))) with hh₀
  have hh₀pos : 0 < h₀ := by
    refine lt_min (lt_min (by positivity) (by linarith [Q.η_pos]))
      (lt_min (by positivity) (lt_min (by positivity) (lt_min one_pos (by positivity))))
  set C₂ : ℝ := |Q.beta| * M * C₁ ^ 2 + 2 / η₀ * C₁ ^ 2 with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  suffices hL : Sφ - Q.alpha * Lφ - Q.beta * Gφ = 0 by linarith
  refine eq_zero_of_mul_le_sq hh₀pos hC₂0 fun h hh => ?_
  have hh1 : |h| ≤ η' / 2 := le_trans hh (le_trans (min_le_left _ _) (min_le_left _ _))
  have hh2 : |h| ≤ Q.η / 2 := le_trans hh (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh3 : |h| ≤ |Q.det| / (4 * mR ^ 2 + 1) :=
    le_trans hh (le_trans (min_le_right _ _) (min_le_left _ _))
  have hh4 : |h| ≤ ρ₀ / Cρ :=
    le_trans hh (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hh5 : |h| ≤ 1 := le_trans hh (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hh6 : |h| ≤ η₀ / (2 * C₁) := le_trans hh (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hC₁h : C₁ * |h| ≤ η₀ / 2 := by
    have h2C : (0:ℝ) < 2 * C₁ := by linarith
    have := (le_div_iff₀ h2C).mp hh6
    linarith
  have hC₁h1 : C₁ * |h| ≤ 1 := by linarith
  have hC₁h0 : 0 ≤ C₁ * |h| := mul_nonneg hC₁0.le (abs_nonneg h)
  -- the perturbed graphon `W + hφ`
  have hfs : ∀ x y, W.toFun x y + h * φ x y = W.toFun y x + h * φ y x := fun x y => by
    rw [W.symm' x y, hφs x y]
  have hfm : Measurable fun p : ℝ × ℝ => W.toFun p.1 p.2 + h * φ p.1 p.2 :=
    W.measurable_uncurry.add (measurable_const.mul hφm)
  set Wh : Graphon := Graphon.ofClamp (fun x y => W.toFun x y + h * φ x y) hfs hfm with hWh
  have hWh_eq : ∀ x y, Wh.toFun x y = W.toFun x y + h * φ x y := by
    intro x y
    refine Graphon.ofClamp_apply_of_mem hfs hfm ?_
    by_cases h0 : φ x y = 0
    · rw [h0, mul_zero, add_zero]; exact W.mem_Icc x y
    · have hW := hφsupp x y h0
      have hb : |h * φ x y| ≤ η' / 2 := by
        rw [abs_mul]
        calc |h| * |φ x y| ≤ (η' / 2) * 1 := mul_le_mul hh1 (hφb x y) (abs_nonneg _) (by positivity)
          _ = η' / 2 := mul_one _
      have := abs_le.mp hb
      constructor <;> linarith [hW.1, hW.2, this.1, this.2]
  -- `Wh` moves the constraints by `O(h)`
  have heWh : Wh.edgeDensity = W.edgeDensity + h * Lφ := by
    have := edgeDensity_add_dirs W Wh (χ₂ := fun _ _ => (0:ℝ)) (u₂ := 0) hφm measurable_const hφb
      (fun _ _ => by simp) (fun x y => by rw [hWh_eq]; ring)
    rw [this]; simp [hLφ]
  have hdiffW : ∀ x y, |Wh.toFun x y - W.toFun x y| ≤ |h| := fun x y => by
    rw [hWh_eq, add_sub_cancel_left, abs_mul]
    calc |h| * |φ x y| ≤ |h| * 1 := mul_le_mul_of_nonneg_left (hφb x y) (abs_nonneg _)
      _ = |h| := mul_one _
  have htWh : |Wh.tDensity H - W.tDensity H| ≤ (mR + M) * |h| := by
    have hexp := Graphon.abs_tDensity_sub_linear_le H W Wh (δ := fun x y => h * φ x y)
      (fun x y => hWh_eq x y) (measurable_const.mul hφm) (abs_nonneg h) hh5
      (fun x y => by
        rw [abs_mul]
        calc |h| * |φ x y| ≤ |h| * 1 := mul_le_mul_of_nonneg_left (hφb x y) (abs_nonneg _)
          _ = |h| := mul_one _)
    have hlin : |∫ p : ℝ × ℝ, h * φ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ| ≤ |h| * mR := by
      have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => h * φ p.1 p.2)
        (g := fun p : ℝ × ℝ => W.gammaW H p.1 p.2) (A := |h|) (B := mR)
        (fun p => by
          rw [abs_mul]
          calc |h| * |φ p.1 p.2| ≤ |h| * 1 := mul_le_mul_of_nonneg_left (hφb _ _) (abs_nonneg _)
            _ = |h| := mul_one _)
        (fun p => by rw [abs_of_nonneg (W.gammaW_nonneg H _ _)]; exact W.gammaW_le H _ _)
      exact this
    have hsq : M * |h| ^ 2 ≤ M * |h| := by
      apply mul_le_mul_of_nonneg_left _ hM0.le
      nlinarith [abs_nonneg h]
    have h1 := abs_sub_abs_le_abs_sub (Wh.tDensity H - W.tDensity H)
      (∫ p : ℝ × ℝ, h * φ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ)
    have hexp' : |Wh.tDensity H - W.tDensity H
        - ∫ p : ℝ × ℝ, h * φ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ| ≤ M * |h| ^ 2 := hexp
    have e : (mR + M) * |h| = |h| * mR + M * |h| := by ring
    linarith only [h1, hexp', hlin, hsq, e]
  -- the correction hypotheses at `Wh`
  have hsuppWh : ∀ x y, Q.χ₁ x y ≠ 0 ∨ Q.χ₂ x y ≠ 0 → Wh.toFun x y ∈ Icc (Q.η / 2) (1 - Q.η / 2) := by
    intro x y hxy
    have hW := Q.supp x y hxy
    have := abs_le.mp (hdiffW x y)
    constructor <;> linarith [hW.1, hW.2, this.1, this.2]
  have hgdiff : ∀ {χ : ℝ → ℝ → ℝ}, (Measurable fun p : ℝ × ℝ => χ p.1 p.2) → (∀ x y, |χ x y| ≤ 1) →
      |∫ p : ℝ × ℝ, χ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ
        - ∫ p : ℝ × ℝ, χ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ| ≤ mR ^ 2 * |h| := by
    intro χ hm hb
    rw [← integral_sub (integrable_bdd_mul_gammaW H Wh hm hb) (integrable_bdd_mul_gammaW H W hm hb)]
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => χ p.1 p.2)
      (g := fun p : ℝ × ℝ => Wh.gammaW H p.1 p.2 - W.gammaW H p.1 p.2) (A := 1)
      (B := mR * (mR * |h|)) (fun p => hb _ _) (fun p => W.abs_gammaW_sub_le H Wh hdiffW _ _)
    have e : ∀ p : ℝ × ℝ, χ p.1 p.2 * Wh.gammaW H p.1 p.2 - χ p.1 p.2 * W.gammaW H p.1 p.2
        = χ p.1 p.2 * (Wh.gammaW H p.1 p.2 - W.gammaW H p.1 p.2) := fun p => by ring
    simp only [e]
    calc _ ≤ 1 * (mR * (mR * |h|)) := this
      _ = mR ^ 2 * |h| := by ring
  have hc₁b : |Q.c₁| ≤ 1 := by
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => Q.χ₁ p.1 p.2)
      (g := fun _ => (1:ℝ)) (A := 1) (B := 1) (fun p => Q.bound₁ _ _) (fun _ => by simp)
    simpa [QualDirs.c₁] using this
  have hc₂b : |Q.c₂| ≤ 1 := by
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => Q.χ₂ p.1 p.2)
      (g := fun _ => (1:ℝ)) (A := 1) (B := 1) (fun p => Q.bound₂ _ _) (fun _ => by simp)
    simpa [QualDirs.c₂] using this
  have hdetWh : |Q.det| / 2 ≤ |(∫ p : ℝ × ℝ, Q.χ₁ p.1 p.2 ∂gμ)
      * (∫ p : ℝ × ℝ, Q.χ₂ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ)
      - (∫ p : ℝ × ℝ, Q.χ₂ p.1 p.2 ∂gμ) * (∫ p : ℝ × ℝ, Q.χ₁ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ)| := by
    have hd1 := hgdiff Q.meas₁ Q.bound₁
    have hd2 := hgdiff Q.meas₂ Q.bound₂
    set g₁' := ∫ p : ℝ × ℝ, Q.χ₁ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ
    set g₂' := ∫ p : ℝ × ℝ, Q.χ₂ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ
    have hdiff : |(Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det| ≤ 2 * mR ^ 2 * |h| := by
      have e : (Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det = Q.c₁ * (g₂' - Q.g₂) - Q.c₂ * (g₁' - Q.g₁) := by
        unfold QualDirs.det; ring
      rw [e]
      calc |Q.c₁ * (g₂' - Q.g₂) - Q.c₂ * (g₁' - Q.g₁)|
          ≤ |Q.c₁| * |g₂' - Q.g₂| + |Q.c₂| * |g₁' - Q.g₁| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ 1 * (mR ^ 2 * |h|) + 1 * (mR ^ 2 * |h|) :=
            add_le_add (mul_le_mul hc₁b hd2 (abs_nonneg _) zero_le_one)
              (mul_le_mul hc₂b hd1 (abs_nonneg _) zero_le_one)
        _ = 2 * mR ^ 2 * |h| := by ring
    have hsmall : 2 * mR ^ 2 * |h| ≤ |Q.det| / 2 := by
      rw [le_div_iff₀ (by positivity)] at hh3
      nlinarith [abs_nonneg h, sq_nonneg mR]
    have := abs_sub_abs_le_abs_sub Q.det ((Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det)
    have e2 : Q.det - ((Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det) = 2 * Q.det - (Q.c₁ * g₂' - Q.c₂ * g₁') := by
      ring
    have h3 : |Q.c₁ * g₂' - Q.c₂ * g₁'| ≥ |Q.det| - |(Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det| := by
      have := abs_sub_abs_le_abs_sub Q.det (Q.det - (Q.c₁ * g₂' - Q.c₂ * g₁'))
      rw [sub_sub_cancel] at this
      have e3 : |Q.det - (Q.c₁ * g₂' - Q.c₂ * g₁')| = |(Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det| :=
        abs_sub_comm _ _
      linarith
    show |Q.det| / 2 ≤ |Q.c₁ * g₂' - Q.c₂ * g₁'|
    linarith
  have hρ : |e₀ - Wh.edgeDensity| + |t₀ - Wh.tDensity H| ≤ ρ₀ := by
    have h1 : |e₀ - Wh.edgeDensity| ≤ |h| := by
      rw [heWh, ← he]
      have : W.edgeDensity - (W.edgeDensity + h * Lφ) = -(h * Lφ) := by ring
      rw [this, abs_neg, abs_mul]
      have hL : |Lφ| ≤ 1 := by
        have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => φ p.1 p.2)
          (g := fun _ => (1:ℝ)) (A := 1) (B := 1) (fun p => hφb _ _) (fun _ => by simp)
        simpa [hLφ] using this
      calc |h| * |Lφ| ≤ |h| * 1 := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
        _ = |h| := mul_one _
    have h2 : |t₀ - Wh.tDensity H| ≤ (mR + M) * |h| := by
      rw [← ht, abs_sub_comm]; exact htWh
    have h3 : Cρ * |h| ≤ ρ₀ := by
      rw [le_div_iff₀ hCρ0] at hh4; linarith
    have h4 : Cρ * |h| = |h| + (mR + M) * |h| := by rw [hCρ]; ring
    linarith
  obtain ⟨u₁, u₂, hu, W'', hW'', he'', ht''⟩ := hcorr Wh Q.χ₁ Q.χ₂ Q.meas₁ Q.meas₂ Q.symm₁ Q.symm₂
    Q.bound₁ Q.bound₂ hsuppWh hdetWh e₀ t₀ hρ
  have hu' : |u₁| + |u₂| ≤ K * Cρ * |h| := by
    have : K * (|e₀ - Wh.edgeDensity| + |t₀ - Wh.tDensity H|) ≤ K * (Cρ * |h|) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      have h1 : |e₀ - Wh.edgeDensity| ≤ |h| := by
        rw [heWh, ← he]
        have : W.edgeDensity - (W.edgeDensity + h * Lφ) = -(h * Lφ) := by ring
        rw [this, abs_neg, abs_mul]
        have hL : |Lφ| ≤ 1 := by
          have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => φ p.1 p.2)
            (g := fun _ => (1:ℝ)) (A := 1) (B := 1) (fun p => hφb _ _) (fun _ => by simp)
          simpa [hLφ] using this
        calc |h| * |Lφ| ≤ |h| * 1 := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
          _ = |h| := mul_one _
      have h2 : |t₀ - Wh.tDensity H| ≤ (mR + M) * |h| := by
        rw [← ht, abs_sub_comm]; exact htWh
      have h4 : Cρ * |h| = |h| + (mR + M) * |h| := by rw [hCρ]; ring
      linarith
    linarith [mul_assoc K Cρ |h|]
  -- `W''` as a perturbation of `W`
  set δ : ℝ → ℝ → ℝ := fun x y => h * φ x y + u₁ * Q.χ₁ x y + u₂ * Q.χ₂ x y with hδ
  have hW''δ : ∀ x y, W''.toFun x y = W.toFun x y + δ x y := fun x y => by
    rw [hW'', hWh_eq]; simp only [hδ]; ring
  have hδm : Measurable fun p : ℝ × ℝ => δ p.1 p.2 :=
    ((measurable_const.mul hφm).add (measurable_const.mul Q.meas₁)).add
      (measurable_const.mul Q.meas₂)
  have hδb : ∀ x y, |δ x y| ≤ C₁ * |h| := by
    intro x y
    have h1 : |δ x y| ≤ |h| + (|u₁| + |u₂|) := by
      simp only [hδ]
      calc |h * φ x y + u₁ * Q.χ₁ x y + u₂ * Q.χ₂ x y|
          ≤ |h * φ x y| + |u₁ * Q.χ₁ x y| + |u₂ * Q.χ₂ x y| := abs_add_three _ _ _
        _ ≤ |h| * 1 + |u₁| * 1 + |u₂| * 1 := by
            rw [abs_mul, abs_mul, abs_mul]
            exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hφb x y) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (Q.bound₁ x y) (abs_nonneg _)))
              (mul_le_mul_of_nonneg_left (Q.bound₂ x y) (abs_nonneg _))
        _ = |h| + (|u₁| + |u₂|) := by ring
    have h2 : C₁ * |h| = |h| + K * Cρ * |h| := by rw [hC₁]; ring
    linarith
  have hδsupp : ∀ x y, δ x y ≠ 0 → W.toFun x y ∈ Icc η₀ (1 - η₀) := by
    intro x y hxy
    by_cases hφ0 : φ x y = 0
    · have hχ : Q.χ₁ x y ≠ 0 ∨ Q.χ₂ x y ≠ 0 := by
        by_contra hc; push Not at hc
        apply hxy; simp only [hδ, hφ0, hc.1, hc.2, mul_zero, add_zero]
      have hW := Q.supp x y hχ
      constructor <;> linarith [hW.1, hW.2, min_le_left Q.η η']
    · have hW := hφsupp x y hφ0
      constructor <;> linarith [hW.1, hW.2, min_le_right Q.η η']
  have hδη : ∀ x y, |δ x y| ≤ η₀ / 2 := fun x y => le_trans (hδb x y) hC₁h
  -- the entropy gain and maximality
  have hent := Graphon.entropy_add_ge W W'' hW''δ hδm hη₀pos hη₀le hδsupp hδη
  have hmaxW'' := hopt W'' he'' ht''
  -- the linear entropy term
  have hint_dφ := integrable_dS0_mul W hφm hφb hη' hφsupp
  have hint_d₁ := integrable_dS0_mul W Q.meas₁ Q.bound₁ Q.η_pos (fun x y h => Q.supp x y (Or.inl h))
  have hint_d₂ := integrable_dS0_mul W Q.meas₂ Q.bound₂ Q.η_pos (fun x y h => Q.supp x y (Or.inr h))
  have hlinS : ∫ p : ℝ × ℝ, dS0 (W.toFun p.1 p.2) * δ p.1 p.2 ∂gμ
      = h * Sφ + u₁ * Q.s₁ + u₂ * Q.s₂ := by
    have e : ∀ p : ℝ × ℝ, dS0 (W.toFun p.1 p.2) * δ p.1 p.2
        = h * (dS0 (W.toFun p.1 p.2) * φ p.1 p.2) + u₁ * (dS0 (W.toFun p.1 p.2) * Q.χ₁ p.1 p.2)
          + u₂ * (dS0 (W.toFun p.1 p.2) * Q.χ₂ p.1 p.2) := fun p => by simp only [hδ]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e),
      integral_lin_three hint_dφ hint_d₁ hint_d₂ h u₁ u₂]
    rfl
  have hsqδ : ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ C₁ ^ 2 * h ^ 2 := by
    have hb : ∀ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ≤ C₁ ^ 2 * h ^ 2 := fun p => by
      have := hδb p.1 p.2
      rw [← sq_abs (δ p.1 p.2), ← sq_abs h]
      calc |δ p.1 p.2| ^ 2 ≤ (C₁ * |h|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = C₁ ^ 2 * |h| ^ 2 := by ring
    calc ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ ∫ _p : ℝ × ℝ, C₁ ^ 2 * h ^ 2 ∂gμ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hb)
      _ = C₁ ^ 2 * h ^ 2 := by simp [gμ]
  -- the constraints at `W''`
  have heW'' : W''.edgeDensity = Wh.edgeDensity + u₁ * Q.c₁ + u₂ * Q.c₂ :=
    edgeDensity_add_dirs Wh W'' Q.meas₁ Q.meas₂ Q.bound₁ Q.bound₂ hW''
  have hecon : h * Lφ + u₁ * Q.c₁ + u₂ * Q.c₂ = 0 := by
    rw [he'', heWh, he] at heW''; linarith
  have htexp := Graphon.abs_tDensity_sub_linear_le H W W'' hW''δ hδm hC₁h0 hC₁h1 hδb
  have hlinT : ∫ p : ℝ × ℝ, δ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ
      = h * Gφ + u₁ * Q.g₁ + u₂ * Q.g₂ := by
    have hiφ := integrable_bdd_mul_gammaW H W hφm hφb
    have hi₁ := integrable_bdd_mul_gammaW H W Q.meas₁ Q.bound₁
    have hi₂ := integrable_bdd_mul_gammaW H W Q.meas₂ Q.bound₂
    have e : ∀ p : ℝ × ℝ, δ p.1 p.2 * W.gammaW H p.1 p.2
        = h * (φ p.1 p.2 * W.gammaW H p.1 p.2) + u₁ * (Q.χ₁ p.1 p.2 * W.gammaW H p.1 p.2)
          + u₂ * (Q.χ₂ p.1 p.2 * W.gammaW H p.1 p.2) := fun p => by simp only [hδ]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e),
      integral_lin_three hiφ hi₁ hi₂ h u₁ u₂]
    rfl
  rw [ht'', ← ht, sub_self, zero_sub, abs_neg, hlinT] at htexp
  -- assemble
  have hαβ₁ := Q.alpha_beta_eq₁
  have hαβ₂ := Q.alpha_beta_eq₂
  have hkey : u₁ * Q.s₁ + u₂ * Q.s₂
      = -(Q.alpha * (h * Lφ)) + Q.beta * (u₁ * Q.g₁ + u₂ * Q.g₂) := by
    rw [← hαβ₁, ← hαβ₂]
    have : Q.alpha * (h * Lφ) = -(Q.alpha * (u₁ * Q.c₁ + u₂ * Q.c₂)) := by
      have : h * Lφ = -(u₁ * Q.c₁ + u₂ * Q.c₂) := by linarith
      rw [this]; ring
    rw [this]; ring
  have hβterm : |Q.beta * (h * Gφ + u₁ * Q.g₁ + u₂ * Q.g₂)| ≤ |Q.beta| * M * C₁ ^ 2 * h ^ 2 := by
    rw [abs_mul]
    calc |Q.beta| * |h * Gφ + u₁ * Q.g₁ + u₂ * Q.g₂| ≤ |Q.beta| * (M * (C₁ * |h|) ^ 2) :=
          mul_le_mul_of_nonneg_left htexp (abs_nonneg _)
      _ = |Q.beta| * M * C₁ ^ 2 * h ^ 2 := by rw [mul_pow, sq_abs]; ring
  have hβl := (abs_le.mp hβterm).1
  have hsqterm : 2 / η₀ * ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ 2 / η₀ * C₁ ^ 2 * h ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsqδ (by positivity : (0:ℝ) ≤ 2 / η₀)
    linarith [mul_assoc (2 / η₀) (C₁ ^ 2) (h ^ 2)]
  rw [hlinS] at hent
  have hfinal : h * (Sφ - Q.alpha * Lφ - Q.beta * Gφ)
      = (h * Sφ + u₁ * Q.s₁ + u₂ * Q.s₂) - Q.beta * (h * Gφ + u₁ * Q.g₁ + u₂ * Q.g₂) := by
    rw [add_assoc (h * Sφ), hkey]; ring
  rw [hfinal, hC₂]
  have e5 : (|Q.beta| * M * C₁ ^ 2 + 2 / η₀ * C₁ ^ 2) * h ^ 2
      = |Q.beta| * M * C₁ ^ 2 * h ^ 2 + 2 / η₀ * C₁ ^ 2 * h ^ 2 := by ring
  rw [e5]
  linarith only [hent, hmaxW'', hβl, hsqterm]

set_option maxHeartbeats 1000000 in
/-- **The Euler–Lagrange equation** (draft `kb:eq:el`): `S₀'(W) = α + β Γ_W` almost everywhere
on `{0 < W < 1}`. -/
theorem QualDirs.el_ae {W : Graphon} {e₀ t₀ : ℝ} (hmax : IsMaximizer H W e₀ t₀)
    (Q : QualDirs H W) :
    ∀ᵐ p ∂gμ, W.toFun p.1 p.2 ∈ Ioo (0:ℝ) 1 →
      dS0 (W.toFun p.1 p.2) = Q.alpha + Q.beta * W.gammaW H p.1 p.2 := by
  classical
  -- it suffices to prove the identity on each `Ω_n = {1/(n+3) ≤ W ≤ 1 - 1/(n+3)}`
  have hlevel : ∀ n : ℕ, ∀ᵐ p ∂gμ, W.toFun p.1 p.2 ∈ Icc (1 / ((n:ℝ) + 3)) (1 - 1 / ((n:ℝ) + 3)) →
      dS0 (W.toFun p.1 p.2) = Q.alpha + Q.beta * W.gammaW H p.1 p.2 := by
    intro n
    set η' : ℝ := 1 / ((n:ℝ) + 3) with hη'
    have hη'pos : 0 < η' := by positivity
    have hη'le : η' ≤ 1 / 2 := by
      rw [hη']; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨L, hL⟩ := exists_abs_dS0_le hη'pos
    set F : ℝ → ℝ → ℝ := fun x y => dS0 (W.toFun x y) - Q.alpha - Q.beta * W.gammaW H x y with hF
    set ind : ℝ → ℝ → ℝ := fun x y =>
      (Icc η' (1 - η')).indicator (fun _ => (1:ℝ)) (W.toFun x y) with hind
    set B : ℝ := max (max L 0 + |Q.alpha| + |Q.beta| * H.edgeFinset.card) 1 with hB
    have hB1 : 1 ≤ B := le_max_right _ _
    have hBpos : 0 < B := by linarith
    set φ : ℝ → ℝ → ℝ := fun x y => F x y * ind x y / B with hφ
    have hind01 : ∀ x y, ind x y ∈ Icc (0:ℝ) 1 := fun x y => by
      by_cases h : W.toFun x y ∈ Icc η' (1 - η')
      · simp only [hind, Set.indicator_of_mem h]; exact ⟨zero_le_one, le_rfl⟩
      · simp only [hind, Set.indicator_of_notMem h]; exact ⟨le_rfl, zero_le_one⟩
    have hFb : ∀ x y, W.toFun x y ∈ Icc η' (1 - η') → |F x y| ≤ B := by
      intro x y hxy
      have h1 : |F x y| ≤ |dS0 (W.toFun x y)| + |Q.alpha| + |Q.beta| * W.gammaW H x y := by
        simp only [hF]
        calc |dS0 (W.toFun x y) - Q.alpha - Q.beta * W.gammaW H x y|
            ≤ |dS0 (W.toFun x y)| + |Q.alpha| + |Q.beta * W.gammaW H x y| := by
              have := abs_sub (dS0 (W.toFun x y) - Q.alpha) (Q.beta * W.gammaW H x y)
              have := abs_sub (dS0 (W.toFun x y)) Q.alpha
              linarith
          _ = |dS0 (W.toFun x y)| + |Q.alpha| + |Q.beta| * W.gammaW H x y := by
              rw [abs_mul, abs_of_nonneg (W.gammaW_nonneg H _ _)]
      have h2 : |Q.beta| * W.gammaW H x y ≤ |Q.beta| * H.edgeFinset.card :=
        mul_le_mul_of_nonneg_left (W.gammaW_le H _ _) (abs_nonneg _)
      have h3 : |dS0 (W.toFun x y)| ≤ max L 0 := le_trans (hL _ hxy) (le_max_left _ _)
      linarith [le_max_left (max L 0 + |Q.alpha| + |Q.beta| * H.edgeFinset.card) 1]
    have hφb : ∀ x y, |φ x y| ≤ 1 := by
      intro x y
      simp only [hφ]
      rw [abs_div, abs_of_pos hBpos, div_le_one hBpos, abs_mul]
      by_cases h : W.toFun x y ∈ Icc η' (1 - η')
      · have hi : ind x y = 1 := by simp only [hind, Set.indicator_of_mem h]
        rw [hi, abs_one, mul_one]; exact hFb x y h
      · have hi : ind x y = 0 := by simp only [hind, Set.indicator_of_notMem h]
        rw [hi, abs_zero, mul_zero]; linarith
    have hFm : Measurable fun p : ℝ × ℝ => F p.1 p.2 :=
      ((measurable_dS0.comp W.measurable_uncurry).sub measurable_const).sub
        (measurable_const.mul (W.measurable_gammaW H))
    have hindm : Measurable fun p : ℝ × ℝ => ind p.1 p.2 :=
      (measurable_const.indicator measurableSet_Icc).comp W.measurable_uncurry
    have hφm : Measurable fun p : ℝ × ℝ => φ p.1 p.2 := (hFm.mul hindm).div_const B
    have hφs : ∀ x y, φ x y = φ y x := fun x y => by
      simp only [hφ, hF, hind, W.symm' x y, W.gammaW_symm H x y]
    have hφsupp : ∀ x y, φ x y ≠ 0 → W.toFun x y ∈ Icc η' (1 - η') := by
      intro x y hxy
      by_contra h
      apply hxy
      simp only [hφ, hind, Set.indicator_of_notMem h, mul_zero, zero_div]
    have hEL := QualDirs.el_linear H hmax Q hφm hφs hφb hη'pos hη'le hφsupp
    -- `∫ F φ = 0`
    have hint_d := integrable_dS0_mul W hφm hφb hη'pos hφsupp
    have hint_φ : Integrable (fun p : ℝ × ℝ => φ p.1 p.2) gμ :=
      integrable_of_abs_le hφm 1 fun p => hφb _ _
    have hint_Γ := integrable_bdd_mul_gammaW H W hφm hφb
    have hFφ : ∫ p : ℝ × ℝ, F p.1 p.2 * φ p.1 p.2 ∂gμ = 0 := by
      have e : ∀ p : ℝ × ℝ, F p.1 p.2 * φ p.1 p.2
          = dS0 (W.toFun p.1 p.2) * φ p.1 p.2 - (Q.alpha * φ p.1 p.2
            + Q.beta * (φ p.1 p.2 * W.gammaW H p.1 p.2)) := fun p => by simp only [hF]; ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e),
        integral_sub (f := fun p : ℝ × ℝ => dS0 (W.toFun p.1 p.2) * φ p.1 p.2)
          (g := fun p : ℝ × ℝ => Q.alpha * φ p.1 p.2 + Q.beta * (φ p.1 p.2 * W.gammaW H p.1 p.2))
          hint_d ((hint_φ.const_mul _).add (hint_Γ.const_mul _)),
        integral_add (f := fun p : ℝ × ℝ => Q.alpha * φ p.1 p.2)
          (g := fun p : ℝ × ℝ => Q.beta * (φ p.1 p.2 * W.gammaW H p.1 p.2))
          (hint_φ.const_mul _) (hint_Γ.const_mul _), integral_const_mul,
        integral_const_mul, hEL, sub_self]
    -- hence `F² ind = 0` a.e.
    have hnonneg : 0 ≤ fun p : ℝ × ℝ => F p.1 p.2 * φ p.1 p.2 := fun p => by
      simp only [hφ]
      have := (hind01 p.1 p.2).1
      have : F p.1 p.2 * (F p.1 p.2 * ind p.1 p.2 / B) = F p.1 p.2 ^ 2 * ind p.1 p.2 / B := by ring
      rw [this]; positivity
    have hintFφ : Integrable (fun p : ℝ × ℝ => F p.1 p.2 * φ p.1 p.2) gμ := by
      refine integrable_of_abs_le (hFm.mul hφm) B fun p => ?_
      by_cases h : W.toFun p.1 p.2 ∈ Icc η' (1 - η')
      · rw [abs_mul]
        calc |F p.1 p.2| * |φ p.1 p.2| ≤ B * 1 :=
              mul_le_mul (hFb _ _ h) (hφb _ _) (abs_nonneg _) hBpos.le
          _ = B := mul_one B
      · have hφ0 : φ p.1 p.2 = 0 := by
          by_contra h'; exact h (hφsupp _ _ h')
        rw [hφ0, mul_zero, abs_zero]; exact hBpos.le
    have hae := (integral_eq_zero_iff_of_nonneg hnonneg hintFφ).mp hFφ
    filter_upwards [hae] with p hp hmem
    have hp' : F p.1 p.2 * φ p.1 p.2 = 0 := hp
    have hi : ind p.1 p.2 = 1 := by simp only [hind, Set.indicator_of_mem hmem]
    simp only [hφ, hi, mul_one] at hp'
    have : F p.1 p.2 ^ 2 / B = 0 := by rw [← hp']; ring
    have hF0 : F p.1 p.2 = 0 := by
      have : F p.1 p.2 ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp this with h | h
        · exact h
        · linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    simp only [hF] at hF0
    linarith
  rw [← ae_all_iff] at hlevel
  filter_upwards [hlevel] with p hp hmem
  -- choose `n` with `1/(n+3) ≤ min (W p) (1 - W p)`
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / min (W.toFun p.1 p.2) (1 - W.toFun p.1 p.2))
  have hmin : 0 < min (W.toFun p.1 p.2) (1 - W.toFun p.1 p.2) :=
    lt_min hmem.1 (by linarith [hmem.2])
  have hsmall : 1 / ((n:ℝ) + 3) ≤ min (W.toFun p.1 p.2) (1 - W.toFun p.1 p.2) := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hmin] at hn
    nlinarith
  refine hp n ⟨le_trans hsmall (min_le_left _ _), ?_⟩
  have := min_le_right (W.toFun p.1 p.2) (1 - W.toFun p.1 p.2)
  linarith

/-! ### The maximizer avoids `0` and `1` -/

theorem S0_eq_binEntropy_half (u : ℝ) : S0 u = Real.binEntropy u / 2 := by
  unfold S0; rw [shannonH_eq_binEntropy]

theorem S0_zero' : S0 0 = 0 := by rw [S0_eq_binEntropy_half]; simp
theorem S0_one' : S0 1 = 0 := by rw [S0_eq_binEntropy_half]; simp
theorem S0_one_sub' (u : ℝ) : S0 (1 - u) = S0 u := by
  rw [S0_eq_binEntropy_half, S0_eq_binEntropy_half, Real.binEntropy_one_sub]

theorem S0_ge_log {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : h * Real.log (1 / h) / 2 ≤ S0 h := by
  rw [S0_eq_binEntropy_half, Real.binEntropy, Real.log_inv, Real.log_inv, one_div, Real.log_inv]
  have hl : Real.log (1 - h) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have : (1 - h) * -Real.log (1 - h) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 4000000 in
/-- **No one-sided entropy gain.**  If perturbations `W_h` of a maximizer, `h`-close in sup norm,
unchanged on the qualifying directions, gain at least `c·S₀(h)` in entropy, then — since
`S₀(h)/h → ∞` while the constraint correction costs `O(h)` — the maximizer was not maximal. -/
theorem QualDirs.no_one_sided_gain {W : Graphon} {e₀ t₀ : ℝ} (hmax : IsMaximizer H W e₀ t₀)
    (Q : QualDirs H W) {c h₀ : ℝ} (hc : 0 < c) (hh₀ : 0 < h₀) (Wf : ℝ → Graphon)
    (hdiff : ∀ h, 0 < h → h ≤ h₀ → ∀ x y, |(Wf h).toFun x y - W.toFun x y| ≤ h)
    (hsame : ∀ h, 0 < h → h ≤ h₀ → ∀ x y, Q.χ₁ x y ≠ 0 ∨ Q.χ₂ x y ≠ 0 →
      (Wf h).toFun x y = W.toFun x y)
    (hgain : ∀ h, 0 < h → h ≤ h₀ → W.entropy + c * S0 h ≤ (Wf h).entropy) : False := by
  classical
  obtain ⟨he, ht, hopt⟩ := hmax
  set mR : ℝ := (H.edgeFinset.card : ℝ) with hmR
  have hmR0 : 0 ≤ mR := Nat.cast_nonneg _
  set M : ℝ := (2:ℝ) ^ H.edgeFinset.card with hM
  have hM0 : 0 < M := by positivity
  have hdetpos : 0 < |Q.det| := abs_pos.mpr Q.det_ne_zero
  obtain ⟨ρ₀, K, hρ₀, hK, hcorr⟩ := exists_correction H (η := Q.η) (D₀ := |Q.det| / 2)
    Q.η_pos Q.η_le (by linarith)
  set Cρ : ℝ := 1 + mR + M with hCρ
  have hCρ0 : 0 < Cρ := by positivity
  set Ku : ℝ := K * Cρ with hKu
  have hKu0 : 0 < Ku := by positivity
  set C₃ : ℝ := (|Q.s₁| + |Q.s₂|) * Ku + 2 / Q.η * Ku ^ 2 with hC₃
  have hC₃0 : 0 ≤ C₃ := by have := Q.η_pos; positivity
  set h₁ : ℝ := min (min h₀ (1 / 2)) (min (|Q.det| / (4 * mR ^ 2 + 1))
    (min (ρ₀ / Cρ) (min (Q.η / (2 * Ku)) (Real.exp (-(2 * C₃ / c + 1)))))) with hh₁
  have hh₁pos : 0 < h₁ := by
    refine lt_min (lt_min hh₀ (by norm_num)) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by have := Q.η_pos; positivity) (Real.exp_pos _))))
  set h : ℝ := h₁ with hhdef
  have hh0 : 0 < h := hh₁pos
  have hhh₀ : h ≤ h₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hh12 : h ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hh3 : h ≤ |Q.det| / (4 * mR ^ 2 + 1) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hh4 : h ≤ ρ₀ / Cρ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hh5 : h ≤ Q.η / (2 * Ku) := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hh6 : h ≤ Real.exp (-(2 * C₃ / c + 1)) := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have habsh : |h| = h := abs_of_pos hh0
  set Wh : Graphon := Wf h with hWh
  have hd := hdiff h hh0 hhh₀
  have hs := hsame h hh0 hhh₀
  -- the constraint displacement
  have heWh : |Wh.edgeDensity - W.edgeDensity| ≤ h := by
    show |∫ p, Wh.toFun p.1 p.2 ∂gμ - ∫ p, W.toFun p.1 p.2 ∂gμ| ≤ h
    rw [← integral_sub Wh.integrable_self W.integrable_self]
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => Wh.toFun p.1 p.2 - W.toFun p.1 p.2)
      (g := fun _ => (1:ℝ)) (A := h) (B := 1) (fun p => hd _ _) (fun _ => by simp)
    simpa using this
  have hδm : Measurable fun p : ℝ × ℝ => Wh.toFun p.1 p.2 - W.toFun p.1 p.2 :=
    Wh.measurable_uncurry.sub W.measurable_uncurry
  have htWh : |Wh.tDensity H - W.tDensity H| ≤ (mR + M) * h := by
    have hexp := Graphon.abs_tDensity_sub_linear_le H W Wh
      (δ := fun x y => Wh.toFun x y - W.toFun x y) (fun x y => by ring) hδm hh0.le
      (by linarith) hd
    have hlin : |∫ p : ℝ × ℝ, (Wh.toFun p.1 p.2 - W.toFun p.1 p.2) * W.gammaW H p.1 p.2 ∂gμ|
        ≤ h * mR :=
      integral_abs_mul_le_of_bound (fun p => hd _ _)
        (fun p => by rw [abs_of_nonneg (W.gammaW_nonneg H _ _)]; exact W.gammaW_le H _ _)
    have hsq : M * h ^ 2 ≤ M * h := mul_le_mul_of_nonneg_left (by nlinarith) hM0.le
    have h1 := abs_sub_abs_le_abs_sub (Wh.tDensity H - W.tDensity H)
      (∫ p : ℝ × ℝ, (Wh.toFun p.1 p.2 - W.toFun p.1 p.2) * W.gammaW H p.1 p.2 ∂gμ)
    have e : (mR + M) * h = h * mR + M * h := by ring
    linarith only [h1, hexp, hlin, hsq, e]
  -- the correction hypotheses at `Wh`
  have hsuppWh : ∀ x y, Q.χ₁ x y ≠ 0 ∨ Q.χ₂ x y ≠ 0 → Wh.toFun x y ∈ Icc Q.η (1 - Q.η) :=
    fun x y hxy => by rw [hs x y hxy]; exact Q.supp x y hxy
  have hc₁b : |Q.c₁| ≤ 1 := by
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => Q.χ₁ p.1 p.2)
      (g := fun _ => (1:ℝ)) (A := 1) (B := 1) (fun p => Q.bound₁ _ _) (fun _ => by simp)
    simpa [QualDirs.c₁] using this
  have hc₂b : |Q.c₂| ≤ 1 := by
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => Q.χ₂ p.1 p.2)
      (g := fun _ => (1:ℝ)) (A := 1) (B := 1) (fun p => Q.bound₂ _ _) (fun _ => by simp)
    simpa [QualDirs.c₂] using this
  have hgdiff : ∀ {χ : ℝ → ℝ → ℝ}, (Measurable fun p : ℝ × ℝ => χ p.1 p.2) → (∀ x y, |χ x y| ≤ 1) →
      |∫ p : ℝ × ℝ, χ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ
        - ∫ p : ℝ × ℝ, χ p.1 p.2 * W.gammaW H p.1 p.2 ∂gμ| ≤ mR ^ 2 * h := by
    intro χ hm hb
    rw [← integral_sub (integrable_bdd_mul_gammaW H Wh hm hb) (integrable_bdd_mul_gammaW H W hm hb)]
    have := integral_abs_mul_le_of_bound (f := fun p : ℝ × ℝ => χ p.1 p.2)
      (g := fun p : ℝ × ℝ => Wh.gammaW H p.1 p.2 - W.gammaW H p.1 p.2) (A := 1)
      (B := mR * (mR * h)) (fun p => hb _ _) (fun p => W.abs_gammaW_sub_le H Wh hd _ _)
    have e : ∀ p : ℝ × ℝ, χ p.1 p.2 * Wh.gammaW H p.1 p.2 - χ p.1 p.2 * W.gammaW H p.1 p.2
        = χ p.1 p.2 * (Wh.gammaW H p.1 p.2 - W.gammaW H p.1 p.2) := fun p => by ring
    simp only [e]
    calc _ ≤ 1 * (mR * (mR * h)) := this
      _ = mR ^ 2 * h := by ring
  have hdetWh : |Q.det| / 2 ≤ |(∫ p : ℝ × ℝ, Q.χ₁ p.1 p.2 ∂gμ)
      * (∫ p : ℝ × ℝ, Q.χ₂ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ)
      - (∫ p : ℝ × ℝ, Q.χ₂ p.1 p.2 ∂gμ) * (∫ p : ℝ × ℝ, Q.χ₁ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ)| := by
    have hd1 := hgdiff Q.meas₁ Q.bound₁
    have hd2 := hgdiff Q.meas₂ Q.bound₂
    set g₁' := ∫ p : ℝ × ℝ, Q.χ₁ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ
    set g₂' := ∫ p : ℝ × ℝ, Q.χ₂ p.1 p.2 * Wh.gammaW H p.1 p.2 ∂gμ
    have hdiff' : |(Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det| ≤ 2 * mR ^ 2 * h := by
      have e : (Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det = Q.c₁ * (g₂' - Q.g₂) - Q.c₂ * (g₁' - Q.g₁) := by
        unfold QualDirs.det; ring
      rw [e]
      calc |Q.c₁ * (g₂' - Q.g₂) - Q.c₂ * (g₁' - Q.g₁)|
          ≤ |Q.c₁| * |g₂' - Q.g₂| + |Q.c₂| * |g₁' - Q.g₁| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ 1 * (mR ^ 2 * h) + 1 * (mR ^ 2 * h) :=
            add_le_add (mul_le_mul hc₁b hd2 (abs_nonneg _) zero_le_one)
              (mul_le_mul hc₂b hd1 (abs_nonneg _) zero_le_one)
        _ = 2 * mR ^ 2 * h := by ring
    have hsmall : 2 * mR ^ 2 * h ≤ |Q.det| / 2 := by
      rw [le_div_iff₀ (by positivity)] at hh3
      nlinarith [sq_nonneg mR]
    have h3 : |Q.c₁ * g₂' - Q.c₂ * g₁'| ≥ |Q.det| - |(Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det| := by
      have := abs_sub_abs_le_abs_sub Q.det (Q.det - (Q.c₁ * g₂' - Q.c₂ * g₁'))
      rw [sub_sub_cancel] at this
      have e3 : |Q.det - (Q.c₁ * g₂' - Q.c₂ * g₁')| = |(Q.c₁ * g₂' - Q.c₂ * g₁') - Q.det| :=
        abs_sub_comm _ _
      linarith
    show |Q.det| / 2 ≤ |Q.c₁ * g₂' - Q.c₂ * g₁'|
    linarith
  have hρ : |e₀ - Wh.edgeDensity| + |t₀ - Wh.tDensity H| ≤ ρ₀ := by
    rw [← he, ← ht, abs_sub_comm, abs_sub_comm (W.tDensity H)]
    have h3 : Cρ * h ≤ ρ₀ := by rw [le_div_iff₀ hCρ0] at hh4; linarith
    have h4 : Cρ * h = h + (mR + M) * h := by rw [hCρ]; ring
    linarith
  obtain ⟨u₁, u₂, hu, W'', hW'', he'', ht''⟩ := hcorr Wh Q.χ₁ Q.χ₂ Q.meas₁ Q.meas₂ Q.symm₁ Q.symm₂
    Q.bound₁ Q.bound₂ hsuppWh hdetWh e₀ t₀ hρ
  have hu' : |u₁| + |u₂| ≤ Ku * h := by
    have h1 : |e₀ - Wh.edgeDensity| + |t₀ - Wh.tDensity H| ≤ Cρ * h := by
      rw [← he, ← ht, abs_sub_comm, abs_sub_comm (W.tDensity H)]
      have h4 : Cρ * h = h + (mR + M) * h := by rw [hCρ]; ring
      linarith
    calc |u₁| + |u₂| ≤ K * (|e₀ - Wh.edgeDensity| + |t₀ - Wh.tDensity H|) := hu
      _ ≤ K * (Cρ * h) := mul_le_mul_of_nonneg_left h1 hK.le
      _ = Ku * h := by rw [hKu]; ring
  -- the entropy of the corrected graphon
  set δ : ℝ → ℝ → ℝ := fun x y => u₁ * Q.χ₁ x y + u₂ * Q.χ₂ x y with hδ
  have hδm : Measurable fun p : ℝ × ℝ => δ p.1 p.2 :=
    (measurable_const.mul Q.meas₁).add (measurable_const.mul Q.meas₂)
  have hδb : ∀ x y, |δ x y| ≤ Ku * h := by
    intro x y
    calc |δ x y| ≤ |u₁| * |Q.χ₁ x y| + |u₂| * |Q.χ₂ x y| := by
          simp only [hδ]; rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |u₁| * 1 + |u₂| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (Q.bound₁ x y) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (Q.bound₂ x y) (abs_nonneg _))
      _ ≤ Ku * h := by linarith
  have hKuh : Ku * h ≤ Q.η / 2 := by
    rw [le_div_iff₀ (by positivity)] at hh5; linarith
  have hδsupp : ∀ x y, δ x y ≠ 0 → Wh.toFun x y ∈ Icc Q.η (1 - Q.η) := by
    intro x y hxy
    have hχ : Q.χ₁ x y ≠ 0 ∨ Q.χ₂ x y ≠ 0 := by
      by_contra hc'; push Not at hc'
      apply hxy; simp only [hδ, hc'.1, hc'.2, mul_zero, add_zero]
    exact hsuppWh x y hχ
  have hent := Graphon.entropy_add_ge Wh W'' (δ := δ) (fun x y => by rw [hW'']; simp only [hδ]; ring)
    hδm Q.η_pos Q.η_le hδsupp (fun x y => le_trans (hδb x y) hKuh)
  have hlinS : ∫ p : ℝ × ℝ, dS0 (Wh.toFun p.1 p.2) * δ p.1 p.2 ∂gμ = u₁ * Q.s₁ + u₂ * Q.s₂ := by
    have e : ∀ p : ℝ × ℝ, dS0 (Wh.toFun p.1 p.2) * δ p.1 p.2
        = u₁ * (dS0 (W.toFun p.1 p.2) * Q.χ₁ p.1 p.2) + u₂ * (dS0 (W.toFun p.1 p.2) * Q.χ₂ p.1 p.2) := by
      intro p
      by_cases hχ : Q.χ₁ p.1 p.2 ≠ 0 ∨ Q.χ₂ p.1 p.2 ≠ 0
      · rw [hs _ _ hχ]; simp only [hδ]; ring
      · push Not at hχ
        simp only [hδ, hχ.1, hχ.2, mul_zero, add_zero]
    have hi₁ := integrable_dS0_mul W Q.meas₁ Q.bound₁ Q.η_pos (fun x y h => Q.supp x y (Or.inl h))
    have hi₂ := integrable_dS0_mul W Q.meas₂ Q.bound₂ Q.η_pos (fun x y h => Q.supp x y (Or.inr h))
    rw [integral_congr_ae (Filter.Eventually.of_forall e),
      integral_add (f := fun p : ℝ × ℝ => u₁ * (dS0 (W.toFun p.1 p.2) * Q.χ₁ p.1 p.2))
        (g := fun p : ℝ × ℝ => u₂ * (dS0 (W.toFun p.1 p.2) * Q.χ₂ p.1 p.2))
        (hi₁.const_mul _) (hi₂.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  have hsqδ : ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ Ku ^ 2 * h ^ 2 := by
    have hb : ∀ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ≤ Ku ^ 2 * h ^ 2 := fun p => by
      rw [← sq_abs (δ p.1 p.2)]
      calc |δ p.1 p.2| ^ 2 ≤ (Ku * h) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hδb _ _) 2
        _ = Ku ^ 2 * h ^ 2 := by ring
    calc ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ ∫ _p : ℝ × ℝ, Ku ^ 2 * h ^ 2 ∂gμ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hb)
      _ = Ku ^ 2 * h ^ 2 := by simp [gμ]
  rw [hlinS] at hent
  have hmaxW'' := hopt W'' he'' ht''
  have hgainh := hgain h hh0 hhh₀
  -- the linear loss
  have hlin_loss : |u₁ * Q.s₁ + u₂ * Q.s₂| ≤ (|Q.s₁| + |Q.s₂|) * (Ku * h) := by
    calc |u₁ * Q.s₁ + u₂ * Q.s₂| ≤ |u₁| * |Q.s₁| + |u₂| * |Q.s₂| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (|u₁| + |u₂|) * (|Q.s₁| + |Q.s₂|) := by
          have h1 := abs_nonneg u₁
          have h2 := abs_nonneg u₂
          have h3 := abs_nonneg Q.s₁
          have h4 := abs_nonneg Q.s₂
          nlinarith
      _ ≤ (Ku * h) * (|Q.s₁| + |Q.s₂|) := mul_le_mul_of_nonneg_right hu' (by positivity)
      _ = (|Q.s₁| + |Q.s₂|) * (Ku * h) := by ring
  have hsq_loss : 2 / Q.η * ∫ p : ℝ × ℝ, δ p.1 p.2 ^ 2 ∂gμ ≤ 2 / Q.η * Ku ^ 2 * h ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsqδ (by have := Q.η_pos; positivity : (0:ℝ) ≤ 2 / Q.η)
    linarith [mul_assoc (2 / Q.η) (Ku ^ 2) (h ^ 2)]
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hS0bound : c * S0 h ≤ C₃ * h := by
    have h1 := (abs_le.mp hlin_loss).1
    have h2 : 2 / Q.η * Ku ^ 2 * h ^ 2 ≤ 2 / Q.η * Ku ^ 2 * h :=
      mul_le_mul_of_nonneg_left hh2 (by have := Q.η_pos; positivity)
    have e : C₃ * h = (|Q.s₁| + |Q.s₂|) * (Ku * h) + 2 / Q.η * Ku ^ 2 * h := by rw [hC₃]; ring
    linarith only [hent, hmaxW'', hgainh, h1, hsq_loss, h2, e]
  -- but `S₀(h) ≥ h log(1/h)/2` and `log(1/h) > 2C₃/c`
  have hlog := S0_ge_log hh0 (by linarith)
  have hloglarge : 2 * C₃ / c + 1 ≤ Real.log (1 / h) := by
    rw [one_div, Real.log_inv, le_neg]
    calc Real.log h ≤ Real.log (Real.exp (-(2 * C₃ / c + 1))) :=
          Real.log_le_log hh0 hh6
      _ = -(2 * C₃ / c + 1) := Real.log_exp _
  have hcontra : c * (h * (2 * C₃ / c + 1) / 2) ≤ C₃ * h := by
    have h1 : h * (2 * C₃ / c + 1) / 2 ≤ h * Real.log (1 / h) / 2 := by
      have := mul_le_mul_of_nonneg_left hloglarge hh0.le
      linarith
    calc c * (h * (2 * C₃ / c + 1) / 2) ≤ c * S0 h :=
          mul_le_mul_of_nonneg_left (le_trans h1 hlog) hc.le
      _ ≤ C₃ * h := hS0bound
  have e : c * (h * (2 * C₃ / c + 1) / 2) = C₃ * h + c * h / 2 := by field_simp
  have : 0 < c * h / 2 := by positivity
  linarith

/-- A symmetric set of positive measure where `W` takes a fixed boundary value can be pushed
inwards. -/
theorem QualDirs.ae_ne_of_boundary {W : Graphon} {e₀ t₀ : ℝ} (hmax : IsMaximizer H W e₀ t₀)
    (Q : QualDirs H W) {v σ : ℝ} (hv : v = 0 ∧ σ = 1 ∨ v = 1 ∧ σ = -1) :
    ∀ᵐ p ∂gμ, W.toFun p.1 p.2 ≠ v := by
  classical
  by_contra hcon
  set Z : Set (ℝ × ℝ) := {p | W.toFun p.1 p.2 = v} with hZ
  have hZm : MeasurableSet Z := measurableSet_eq_fun W.measurable_uncurry measurable_const
  have hZne : gμ Z ≠ 0 := by
    intro h0
    apply hcon
    rw [ae_iff]
    simpa [hZ] using h0
  have hZpos : 0 < (gμ Z).toReal := ENNReal.toReal_pos hZne (measure_ne_top _ _)
  set φ : ℝ → ℝ → ℝ := fun x y => Z.indicator (fun _ => (1:ℝ)) (x, y) with hφ
  have hφs : ∀ x y, φ x y = φ y x := fun x y => by
    by_cases h : W.toFun x y = v
    · have h' : W.toFun y x = v := by rw [← W.symm' x y]; exact h
      simp only [hφ, Set.indicator_of_mem (show (x, y) ∈ Z from h),
        Set.indicator_of_mem (show (y, x) ∈ Z from h')]
    · have h' : ¬ W.toFun y x = v := by rw [← W.symm' x y]; exact h
      simp only [hφ, Set.indicator_of_notMem (show (x, y) ∉ Z from h),
        Set.indicator_of_notMem (show (y, x) ∉ Z from h')]
  have hφm : Measurable fun p : ℝ × ℝ => φ p.1 p.2 := measurable_const.indicator hZm
  have hφ01 : ∀ x y, φ x y = 1 ∧ W.toFun x y = v ∨ φ x y = 0 ∧ W.toFun x y ≠ v := fun x y => by
    by_cases h : W.toFun x y = v
    · left; exact ⟨by simp only [hφ, Set.indicator_of_mem (show (x, y) ∈ Z from h)], h⟩
    · right; exact ⟨by simp only [hφ, Set.indicator_of_notMem (show (x, y) ∉ Z from h)], h⟩
  have hfs : ∀ h : ℝ, ∀ x y, W.toFun x y + h * σ * φ x y = W.toFun y x + h * σ * φ y x :=
    fun h x y => by rw [W.symm' x y, hφs x y]
  have hfm : ∀ h : ℝ, Measurable fun p : ℝ × ℝ => W.toFun p.1 p.2 + h * σ * φ p.1 p.2 :=
    fun h => W.measurable_uncurry.add (measurable_const.mul hφm)
  set Wf : ℝ → Graphon := fun h =>
    Graphon.ofClamp (fun x y => W.toFun x y + h * σ * φ x y) (hfs h) (hfm h) with hWf
  have hWf_eq : ∀ h, 0 < h → h ≤ 1 / 2 → ∀ x y, (Wf h).toFun x y = W.toFun x y + h * σ * φ x y := by
    intro h hh0 hh1 x y
    refine Graphon.ofClamp_apply_of_mem (hfs h) (hfm h) ?_
    rcases hφ01 x y with ⟨h1, h2⟩ | ⟨h1, _⟩
    · rw [h1, h2]
      rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · constructor <;> linarith
      · constructor <;> linarith
    · rw [h1, mul_zero, add_zero]; exact W.mem_Icc x y
  refine Q.no_one_sided_gain H hmax (c := (gμ Z).toReal) (h₀ := 1 / 2) hZpos (by norm_num) Wf
    ?_ ?_ ?_
  · intro h hh0 hh1 x y
    rw [hWf_eq h hh0 hh1, add_sub_cancel_left]
    have hσ : |σ| = 1 := by rcases hv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
    rcases hφ01 x y with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1, mul_one, abs_mul, hσ, mul_one, abs_of_pos hh0]
    · rw [h1, mul_zero, abs_zero]; exact hh0.le
  · intro h hh0 hh1 x y hχ
    rw [hWf_eq h hh0 hh1]
    have hW := Q.supp x y hχ
    have hne : W.toFun x y ≠ v := by
      rcases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · intro h'; rw [h'] at hW; linarith [hW.1, Q.η_pos]
      · intro h'; rw [h'] at hW; linarith [hW.2, Q.η_pos]
    rcases hφ01 x y with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact absurd h2 hne
    · rw [h1, mul_zero, add_zero]
  · intro h hh0 hh1
    rw [W.entropy_eq_integral_S0, (Wf h).entropy_eq_integral_S0]
    have hpt : ∀ p : ℝ × ℝ, S0 ((Wf h).toFun p.1 p.2) = S0 (W.toFun p.1 p.2) + S0 h * φ p.1 p.2 := by
      intro p
      rw [hWf_eq h hh0 hh1]
      rcases hφ01 p.1 p.2 with ⟨h1, h2⟩ | ⟨h1, _⟩
      · rw [h1, h2, mul_one, mul_one]
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [S0_zero', zero_add, mul_one, zero_add]
        · rw [S0_one', zero_add, show (1:ℝ) + h * -1 = 1 - h by ring, S0_one_sub']
      · rw [h1, mul_zero, add_zero, mul_zero, add_zero]
    have hS0c : Continuous S0 := by
      have e : S0 = fun u => Real.binEntropy u / 2 := funext S0_eq_binEntropy_half
      rw [e]; exact Real.binEntropy_continuous.div_const 2
    have hint1 : Integrable (fun p : ℝ × ℝ => S0 (W.toFun p.1 p.2)) gμ :=
      W.integrable_comp hS0c.measurable hS0c.continuousOn
    have hint2 : Integrable (fun p : ℝ × ℝ => S0 h * φ p.1 p.2) gμ :=
      (integrable_of_abs_le hφm 1 fun p => by
        rcases hφ01 p.1 p.2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> simp).const_mul _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add (f := fun p : ℝ × ℝ => S0 (W.toFun p.1 p.2))
        (g := fun p : ℝ × ℝ => S0 h * φ p.1 p.2) hint1 hint2, integral_const_mul]
    have hφint : ∫ p : ℝ × ℝ, φ p.1 p.2 ∂gμ = (gμ Z).toReal := integral_indicator_one hZm
    rw [hφint, mul_comm]

/-- **The Euler–Lagrange equation with interior values** (draft `kb:lem:el`). -/
theorem QualDirs.el {W : Graphon} {e₀ t₀ : ℝ} (hmax : IsMaximizer H W e₀ t₀)
    (Q : QualDirs H W) :
    ∀ᵐ p ∂gμ, W.toFun p.1 p.2 ∈ Ioo (0:ℝ) 1 ∧
      dS0 (W.toFun p.1 p.2) = Q.alpha + Q.beta * W.gammaW H p.1 p.2 := by
  filter_upwards [Q.el_ae H hmax, Q.ae_ne_of_boundary H hmax (v := 0) (σ := 1) (Or.inl ⟨rfl, rfl⟩),
    Q.ae_ne_of_boundary H hmax (v := 1) (σ := -1) (Or.inr ⟨rfl, rfl⟩)] with p hEL h0 h1
  have hmem : W.toFun p.1 p.2 ∈ Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne (W.nonneg' _ _) (Ne.symm h0), lt_of_le_of_ne (W.le_one' _ _) h1⟩
  exact ⟨hmem, hEL hmem⟩

end UpperTailOptimizers
