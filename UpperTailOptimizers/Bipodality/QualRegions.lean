import UpperTailOptimizers.Bipodality.Multipliers

/-!
# The two regions of a competitor

For a competitor `W` (structure: close to a cross `W₀^I`) we exhibit the two regions used by
`Graphon.exists_qualDirs_of_regions`:

* `E₁`: pairs of rows `L¹`-close to `ε` where `W ≈ ε`; there `Γ_W ≈ m ε^{m-1}`;
* `E₂`: a row of `I` close to its cross row against a row close to `ε`, where `W ≈ ζ`; there
  `Γ_W ≈ m ε^{m-d} ζ^{d-1}`.

This file contains the measure-theoretic estimates.
-/

namespace UpperTailOptimizers

open MeasureTheory Set

/-! ### Markov bounds -/

theorem unitμ_markov {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {C : ℝ}
    (hfb : ∀ x, f x ≤ C) {ω : ℝ} (hω : 0 < ω) :
    (unitμ {x | ω < f x}).toReal ≤ (∫ x, f x ∂unitμ) / ω := by
  have hint : Integrable f unitμ := integrable_of_abs_le hf C fun x => by
    rw [abs_of_nonneg (hf0 x)]; exact hfb x
  have hm : MeasurableSet {x | ω < f x} := measurableSet_lt measurable_const hf
  rw [le_div_iff₀ hω]
  have h1 : ∫ x in {x | ω < f x}, ω ∂unitμ ≤ ∫ x in {x | ω < f x}, f x ∂unitμ :=
    setIntegral_mono_on (integrable_const ω).integrableOn hint.integrableOn hm
      (fun x hx => le_of_lt hx)
  have h2 : ∫ x in {x | ω < f x}, f x ∂unitμ ≤ ∫ x, f x ∂unitμ :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hf0)
  rw [setIntegral_const, smul_eq_mul] at h1
  simp only [Measure.real] at h1
  linarith

theorem gμ_markov {f : ℝ × ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ p, 0 ≤ f p) {C : ℝ}
    (hfb : ∀ p, f p ≤ C) {ω : ℝ} (hω : 0 < ω) :
    (gμ {p | ω < f p}).toReal ≤ (∫ p, f p ∂gμ) / ω := by
  have hint : Integrable f gμ := integrable_of_abs_le hf C fun p => by
    rw [abs_of_nonneg (hf0 p)]; exact hfb p
  have hm : MeasurableSet {p | ω < f p} := measurableSet_lt measurable_const hf
  rw [le_div_iff₀ hω]
  have h1 : ∫ p in {p | ω < f p}, ω ∂gμ ≤ ∫ p in {p | ω < f p}, f p ∂gμ :=
    setIntegral_mono_on (integrable_const ω).integrableOn hint.integrableOn hm
      (fun p hp => le_of_lt hp)
  have h2 : ∫ p in {p | ω < f p}, f p ∂gμ ≤ ∫ p, f p ∂gμ :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hf0)
  rw [setIntegral_const, smul_eq_mul] at h1
  simp only [Measure.real] at h1
  linarith

/-! ### Row distances -/

namespace Graphon

theorem measurable_rowDist (W : Graphon) (ε : ℝ) : Measurable fun x => W.rowDist ε x :=
  (((W.measurable_uncurry.sub measurable_const).abs).stronglyMeasurable).integral_prod_right'.measurable

theorem rowDist_le_one (W : Graphon) {ε : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (x : ℝ) :
    W.rowDist ε x ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := unitμ) (f := fun t => |W.toFun x t - ε|)
    (C := 1) (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_abs]
      have := W.mem_Icc x t
      rw [abs_le]; constructor <;> linarith [this.1, this.2, hε.1, hε.2])
  have h' : |W.rowDist ε x| ≤ 1 := by
    show |∫ t, |W.toFun x t - ε| ∂unitμ| ≤ 1
    simpa [measureReal_def] using h
  exact le_trans (le_abs_self _) h'

theorem integral_rowDist (W : Graphon) (ε : ℝ) :
    ∫ x, W.rowDist ε x ∂unitμ = W.constDist ε := by
  have hint : Integrable (fun p : ℝ × ℝ => |W.toFun p.1 p.2 - ε|) gμ :=
    integrable_of_abs_le ((W.measurable_uncurry.sub measurable_const).abs) (1 + |ε|) fun p => by
      rw [abs_abs]
      have := W.mem_Icc p.1 p.2
      calc |W.toFun p.1 p.2 - ε| ≤ |W.toFun p.1 p.2| + |ε| := abs_sub _ _
        _ ≤ 1 + |ε| := by rw [abs_of_nonneg this.1]; linarith [this.2]
  exact integral_integral hint

theorem constDist_le_sqrt (W : Graphon) (ε : ℝ) :
    W.constDist ε ≤ Real.sqrt (∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - ε) ^ 2 ∂gμ) := by
  have hm : Measurable fun p : ℝ × ℝ => W.toFun p.1 p.2 - ε := W.measurable_uncurry.sub measurable_const
  have hb : ∀ p : ℝ × ℝ, |W.toFun p.1 p.2 - ε| ≤ 1 + |ε| := fun p => by
    have := W.mem_Icc p.1 p.2
    calc |W.toFun p.1 p.2 - ε| ≤ |W.toFun p.1 p.2| + |ε| := abs_sub _ _
      _ ≤ 1 + |ε| := by rw [abs_of_nonneg this.1]; linarith [this.2]
  have hi : Integrable (fun p : ℝ × ℝ => W.toFun p.1 p.2 - ε) gμ := integrable_of_abs_le hm _ hb
  have hi2 : Integrable (fun p : ℝ × ℝ => (W.toFun p.1 p.2 - ε) ^ 2) gμ :=
    integrable_of_abs_le (hm.pow_const 2) ((1 + |ε|) ^ 2) fun p => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb p) 2
  have : IsProbabilityMeasure gμ := by unfold gμ; infer_instance
  exact SingularEndpoint.integral_abs_le_sqrt hi hi2

/-- The degree is within the row distance of `ε`. -/
theorem abs_degFun_sub_le_rowDist (W : Graphon) (ε x : ℝ) : |W.degFun x - ε| ≤ W.rowDist ε x := by
  have hint := W.integrable_row x
  have h : W.degFun x - ε = ∫ t, (W.toFun x t - ε) ∂unitμ := by
    rw [integral_sub hint (integrable_const ε)]
    simp [degFun]
  rw [h]
  exact abs_integral_le_integral_abs

end Graphon

/-! ### Lipschitz bound for `S₀'` away from the boundary -/

theorem abs_dS0_sub_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) {w w' : ℝ}
    (hw : w ∈ Icc η (1 - η)) (hw' : w' ∈ Icc η (1 - η)) :
    |dS0 w - dS0 w'| ≤ 1 / η * |w - w'| := by
  have hbound : ∀ u ∈ Set.uIcc w' w, ‖-1 / (2 * (u * (1 - u)))‖ ≤ 1 / η := by
    intro u hu
    have hu' : u ∈ Icc η (1 - η) := Set.uIcc_subset_Icc hw' hw hu
    have hprod : η / 2 ≤ u * (1 - u) := by nlinarith [hu'.1, hu'.2]
    have hpos : 0 < 2 * (u * (1 - u)) := by nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_of_pos hpos, div_le_div_iff₀ hpos hη]
    nlinarith
  have h := (convex_uIcc w' w).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := dS0) (f' := fun u => -1 / (2 * (u * (1 - u))))
    (fun u hu => by
      have hu' : u ∈ Icc η (1 - η) := Set.uIcc_subset_Icc hw' hw hu
      have h0 : u ≠ 0 := by intro h; rw [h] at hu'; linarith [hu'.1]
      have h1 : u ≠ 1 := by intro h; rw [h] at hu'; linarith [hu'.2]
      exact (hasDerivAt_dS0 h0 h1).hasDerivWithinAt) hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using h

/-! ### Cross rows -/

namespace Graphon

/-- The `L¹` distance of the row of `x` from the corresponding row of the cross `W₀^I`. -/
noncomputable def crossRowDist (W : Graphon) (ε ζ : ℝ) (I : Set ℝ) (x : ℝ) : ℝ :=
  ∫ t, |W.toFun x t - crossProfile ε ζ I (x, t)| ∂unitμ

theorem measurable_crossProfile (ε ζ : ℝ) {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable (crossProfile ε ζ I) :=
  measurable_const.add (measurable_const.mul (measurable_const.indicator (measurableSet_crossSet hI)))

theorem crossProfile_mem_Icc {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (hζ : ζ ∈ Icc (0:ℝ) 1) (I : Set ℝ)
    (p : ℝ × ℝ) : crossProfile ε ζ I p ∈ Icc (0:ℝ) 1 := by
  unfold crossProfile
  by_cases h : p ∈ crossSet I
  · rw [Set.indicator_of_mem h, mul_one, add_sub_cancel]; exact hζ
  · rw [Set.indicator_of_notMem h, mul_zero, add_zero]; exact hε

theorem measurable_crossRowDist (W : Graphon) (ε ζ : ℝ) {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable fun x => W.crossRowDist ε ζ I x :=
  (((W.measurable_uncurry.sub (measurable_crossProfile ε ζ hI)).abs).stronglyMeasurable).integral_prod_right'.measurable

theorem crossRowDist_nonneg (W : Graphon) (ε ζ : ℝ) (I : Set ℝ) (x : ℝ) :
    0 ≤ W.crossRowDist ε ζ I x := integral_nonneg fun _ => abs_nonneg _

theorem crossRowDist_le_one (W : Graphon) {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (hζ : ζ ∈ Icc (0:ℝ) 1)
    (I : Set ℝ) (x : ℝ) : W.crossRowDist ε ζ I x ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := unitμ)
    (f := fun t => |W.toFun x t - crossProfile ε ζ I (x, t)|) (C := 1)
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_abs]
      have h1 := W.mem_Icc x t
      have h2 := crossProfile_mem_Icc hε hζ I (x, t)
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])
  have h' : |W.crossRowDist ε ζ I x| ≤ 1 := by
    show |∫ t, |W.toFun x t - crossProfile ε ζ I (x, t)| ∂unitμ| ≤ 1
    simpa [measureReal_def] using h
  exact le_trans (le_abs_self _) h'

/-- A row of `I` close to its cross row has degree close to `ζ`. -/
theorem abs_degFun_sub_zeta_le (W : Graphon) {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (hζ : ζ ∈ Icc (0:ℝ) 1)
    {I : Set ℝ} (hI : MeasurableSet I) {x : ℝ} (hx : x ∈ I) :
    |W.degFun x - ζ| ≤ W.crossRowDist ε ζ I x + (unitμ I).toReal := by
  have hrow : ∀ t, crossProfile ε ζ I (x, t) = ζ - (ζ - ε) * I.indicator (fun _ => (1:ℝ)) t := by
    intro t
    unfold crossProfile
    by_cases ht : t ∈ I
    · have hnot : (x, t) ∉ crossSet I := by
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h ht
        · exact h hx
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem ht]; ring
    · have hin : (x, t) ∈ crossSet I := Or.inl ⟨hx, ht⟩
      rw [Set.indicator_of_mem hin, Set.indicator_of_notMem ht]; ring
  have hint_row := W.integrable_row x
  have hind : Integrable (fun t => I.indicator (fun _ => (1:ℝ)) t) unitμ :=
    integrable_of_abs_le (measurable_const.indicator hI) 1 fun t => by
      by_cases ht : t ∈ I
      · rw [Set.indicator_of_mem ht]; simp
      · rw [Set.indicator_of_notMem ht]; simp
  have hI1 : ∫ t, I.indicator (fun _ => (1:ℝ)) t ∂unitμ = (unitμ I).toReal :=
    integral_indicator_one hI
  have hcross : ∫ t, crossProfile ε ζ I (x, t) ∂unitμ = ζ - (ζ - ε) * (unitμ I).toReal := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hrow),
      integral_sub (integrable_const ζ) (hind.const_mul _), integral_const_mul, hI1]
    simp [measureReal_def]
  have hcross_int : Integrable (fun t => crossProfile ε ζ I (x, t)) unitμ :=
    integrable_of_abs_le ((measurable_crossProfile ε ζ hI).comp (measurable_const.prodMk measurable_id)) 1
      fun t => by
        have := crossProfile_mem_Icc hε hζ I (x, t)
        rw [abs_of_nonneg this.1]; exact this.2
  have h1 : |W.degFun x - ∫ t, crossProfile ε ζ I (x, t) ∂unitμ| ≤ W.crossRowDist ε ζ I x := by
    rw [show W.degFun x = ∫ t, W.toFun x t ∂unitμ from rfl, ← integral_sub hint_row hcross_int]
    exact abs_integral_le_integral_abs
  have hI01 : (unitμ I).toReal ≤ 1 := by
    have : unitμ I ≤ 1 := prob_le_one
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have h2 : |ζ - ε| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hε.1, hε.2, hζ.1, hζ.2]
  have h3 : |(ζ - ε) * (unitμ I).toReal| ≤ (unitμ I).toReal := by
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    calc |ζ - ε| * (unitμ I).toReal ≤ 1 * (unitμ I).toReal :=
          mul_le_mul_of_nonneg_right h2 ENNReal.toReal_nonneg
      _ = (unitμ I).toReal := one_mul _
  rw [hcross] at h1
  calc |W.degFun x - ζ| = |(W.degFun x - (ζ - (ζ - ε) * (unitμ I).toReal))
        - (ζ - ε) * (unitμ I).toReal| := by ring_nf
    _ ≤ |W.degFun x - (ζ - (ζ - ε) * (unitμ I).toReal)| + |(ζ - ε) * (unitμ I).toReal| :=
        abs_sub _ _
    _ ≤ W.crossRowDist ε ζ I x + (unitμ I).toReal := add_le_add h1 h3

/-- `∫_I ρ ≤ |I|^{1/2} ‖W - W₀‖₂`. -/
theorem integral_indicator_crossRowDist_le (W : Graphon) {ε ζ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1)
    (hζ : ζ ∈ Icc (0:ℝ) 1) {I : Set ℝ} (hI : MeasurableSet I) :
    ∫ x, I.indicator (fun _ => (1:ℝ)) x * W.crossRowDist ε ζ I x ∂unitμ
      ≤ Real.sqrt (unitμ I).toReal
        * Real.sqrt (∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2 ∂gμ) := by
  set ρ := W.crossRowDist ε ζ I with hρ
  have hρm := W.measurable_crossRowDist ε ζ hI
  have hind : Measurable fun x => I.indicator (fun _ => (1:ℝ)) x := measurable_const.indicator hI
  have hindb : ∀ x, |I.indicator (fun _ => (1:ℝ)) x| ≤ 1 := fun x => by
    by_cases hx : x ∈ I
    · rw [Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx]; simp
  have hρb : ∀ x, |ρ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (W.crossRowDist_nonneg ε ζ I x)]; exact W.crossRowDist_le_one hε hζ I x
  have hi1 : Integrable (fun x => I.indicator (fun _ => (1:ℝ)) x ^ 2) unitμ :=
    integrable_of_abs_le (hind.pow_const 2) 1 fun x => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      nlinarith [hindb x, abs_nonneg (I.indicator (fun _ => (1:ℝ)) x)]
  have hi2 : Integrable (fun x => ρ x ^ 2) unitμ :=
    integrable_of_abs_le (hρm.pow_const 2) 1 fun x => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      nlinarith [hρb x, abs_nonneg (ρ x)]
  have hi12 : Integrable (fun x => I.indicator (fun _ => (1:ℝ)) x * ρ x) unitμ :=
    integrable_of_abs_le (hind.mul hρm) 1 fun x => by
      rw [abs_mul]; nlinarith [hindb x, hρb x, abs_nonneg (I.indicator (fun _ => (1:ℝ)) x),
        abs_nonneg (ρ x)]
  have hcs := SingularEndpoint.integral_mul_le_sqrt_mul_sqrt hi1 hi2 hi12
  have hsq1 : ∫ x, I.indicator (fun _ => (1:ℝ)) x ^ 2 ∂unitμ = (unitμ I).toReal := by
    have : (fun x => I.indicator (fun _ => (1:ℝ)) x ^ 2) = I.indicator (fun _ => (1:ℝ)) := by
      funext x; by_cases hx : x ∈ I
      · rw [Set.indicator_of_mem hx]; norm_num
      · rw [Set.indicator_of_notMem hx]; norm_num
    rw [this]; exact integral_indicator_one hI
  -- `∫ ρ² ≤ ‖W - W₀‖₂²`
  have hsq2 : ∫ x, ρ x ^ 2 ∂unitμ ≤ ∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2 ∂gμ := by
    have hdm : Measurable fun p : ℝ × ℝ => W.toFun p.1 p.2 - crossProfile ε ζ I p :=
      W.measurable_uncurry.sub (measurable_crossProfile ε ζ hI)
    have hdb : ∀ p : ℝ × ℝ, |W.toFun p.1 p.2 - crossProfile ε ζ I p| ≤ 1 := fun p => by
      have h1 := W.mem_Icc p.1 p.2
      have h2 := crossProfile_mem_Icc hε hζ I p
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hint2 : Integrable (fun p : ℝ × ℝ => (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2) gμ :=
      integrable_of_abs_le (hdm.pow_const 2) 1 fun p => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; nlinarith [hdb p, abs_nonneg (W.toFun p.1 p.2 - crossProfile ε ζ I p)]
    have hrow : ∀ x, ρ x ^ 2 ≤ ∫ t, (W.toFun x t - crossProfile ε ζ I (x, t)) ^ 2 ∂unitμ := by
      intro x
      have hm : Measurable fun t => W.toFun x t - crossProfile ε ζ I (x, t) :=
        hdm.comp (measurable_const.prodMk measurable_id)
      have hi : Integrable (fun t => W.toFun x t - crossProfile ε ζ I (x, t)) unitμ :=
        integrable_of_abs_le hm 1 fun t => hdb (x, t)
      have hi' : Integrable (fun t => (W.toFun x t - crossProfile ε ζ I (x, t)) ^ 2) unitμ :=
        integrable_of_abs_le (hm.pow_const 2) 1 fun t => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; nlinarith [hdb (x, t), abs_nonneg (W.toFun x t - crossProfile ε ζ I (x, t))]
      have h := SingularEndpoint.integral_abs_le_sqrt hi hi'
      have h0 : 0 ≤ ∫ t, (W.toFun x t - crossProfile ε ζ I (x, t)) ^ 2 ∂unitμ :=
        integral_nonneg fun _ => sq_nonneg _
      calc ρ x ^ 2 ≤ Real.sqrt (∫ t, (W.toFun x t - crossProfile ε ζ I (x, t)) ^ 2 ∂unitμ) ^ 2 :=
            pow_le_pow_left₀ (W.crossRowDist_nonneg ε ζ I x) h 2
        _ = ∫ t, (W.toFun x t - crossProfile ε ζ I (x, t)) ^ 2 ∂unitμ := Real.sq_sqrt h0
    calc ∫ x, ρ x ^ 2 ∂unitμ
        ≤ ∫ x, ∫ t, (W.toFun x t - crossProfile ε ζ I (x, t)) ^ 2 ∂unitμ ∂unitμ :=
          integral_mono hi2 hint2.integral_prod_left hrow
      _ = ∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2 ∂gμ := integral_integral hint2
  rw [hsq1] at hcs
  exact le_trans hcs (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq2) (Real.sqrt_nonneg _))

end Graphon

/-! ### The regions -/

theorem abs_pow_pred_sub_le {d : ℕ} (hd : 1 ≤ d) {u c : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hc : c ∈ Icc (0:ℝ) 1) : |u ^ (d - 1) - c ^ (d - 1)| ≤ ((d : ℝ) - 1) * |u - c| := by
  have h := _root_.abs_pow_sub_pow_le (a := u) (b := c) (n := d - 1)
  have hmax : max |u| |c| ^ (d - 1 - 1) ≤ 1 := by
    apply pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
    exact max_le (by rw [abs_of_nonneg hu.1]; exact hu.2) (by rw [abs_of_nonneg hc.1]; exact hc.2)
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  rw [hcast] at h
  have hd1 : (0:ℝ) ≤ (d : ℝ) - 1 := by
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  calc |u ^ (d - 1) - c ^ (d - 1)| ≤ |u - c| * ((d : ℝ) - 1) * max |u| |c| ^ (d - 1 - 1) := h
    _ ≤ |u - c| * ((d : ℝ) - 1) * 1 := mul_le_mul_of_nonneg_left hmax (mul_nonneg (abs_nonneg _) hd1)
    _ = ((d : ℝ) - 1) * |u - c| := by ring

namespace Graphon

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

set_option maxHeartbeats 4000000 in
/-- **The two regions of a competitor.** -/
theorem exists_regions (W : Graphon) {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    {ε ζ ω τ : ℝ} (hε : ε ∈ Icc (0:ℝ) 1) (hζ : ζ ∈ Icc (0:ℝ) 1) (hω : 0 < ω) (hτ : 0 < τ)
    {I : Set ℝ} (hI : MeasurableSet I) (hIpos : 0 < (unitμ I).toReal)
    (hQω : W.constDist ε / ω ≤ 1 / 2) (hQτ : W.constDist ε / τ ≤ 1 / 8)
    (hrω : Real.sqrt (unitμ I).toReal
        * Real.sqrt (∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2 ∂gμ) / ω
        ≤ (unitμ I).toReal / 2)
    (hrτ : (∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2 ∂gμ) / τ ^ 2
        ≤ (unitμ I).toReal / 16)
    (hIsmall : (unitμ I).toReal ≤ 1 / 16) :
    ∃ E₁ E₂ : Set (ℝ × ℝ), MeasurableSet E₁ ∧ MeasurableSet E₂ ∧
      (∀ x y, (x, y) ∈ E₁ ↔ (y, x) ∈ E₁) ∧ (∀ x y, (x, y) ∈ E₂ ↔ (y, x) ∈ E₂) ∧
      0 < (gμ E₁).toReal ∧ 0 < (gμ E₂).toReal ∧
      (∀ p ∈ E₁, |W.toFun p.1 p.2 - ε| ≤ τ) ∧ (∀ p ∈ E₂, |W.toFun p.1 p.2 - ζ| ≤ τ) ∧
      (∀ p ∈ E₁, |W.gammaW H p.1 p.2
          - H.edgeFinset.card * (ε ^ (H.edgeFinset.card - d) * ε ^ (d - 1))|
        ≤ H.edgeFinset.card * (H.edgeFinset.card * (ω + W.constDist ε))
          + H.edgeFinset.card * ((d : ℝ) - 1) * (ω + (unitμ I).toReal)) ∧
      (∀ p ∈ E₂, |W.gammaW H p.1 p.2
          - H.edgeFinset.card * (ε ^ (H.edgeFinset.card - d) * ζ ^ (d - 1))|
        ≤ H.edgeFinset.card * (H.edgeFinset.card * (ω + W.constDist ε))
          + H.edgeFinset.card * ((d : ℝ) - 1) * (ω + (unitμ I).toReal)) := by
  classical
  set mR : ℝ := (H.edgeFinset.card : ℝ) with hmR
  have hmR0 : 0 ≤ mR := Nat.cast_nonneg _
  have hd1 : (0:ℝ) ≤ (d : ℝ) - 1 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set Q₁ : ℝ := W.constDist ε with hQ₁
  have hQ₁0 : 0 ≤ Q₁ := W.constDist_nonneg ε
  set iI : ℝ := (unitμ I).toReal with hiI
  set G₁ : Set ℝ := {x | W.rowDist ε x ≤ ω} with hG₁
  set G₂ : Set ℝ := I ∩ {x | W.crossRowDist ε ζ I x ≤ ω} with hG₂
  have hG₁m : MeasurableSet G₁ := measurableSet_le (W.measurable_rowDist ε) measurable_const
  have hG₂m : MeasurableSet G₂ :=
    hI.inter (measurableSet_le (W.measurable_crossRowDist ε ζ hI) measurable_const)
  set E₁ : Set (ℝ × ℝ) := {p | p.1 ∈ G₁ ∧ p.2 ∈ G₁ ∧ |W.toFun p.1 p.2 - ε| ≤ τ} with hE₁
  set E₂ : Set (ℝ × ℝ) := {p | ((p.1 ∈ G₂ ∧ p.2 ∈ G₁) ∨ (p.2 ∈ G₂ ∧ p.1 ∈ G₁))
    ∧ |W.toFun p.1 p.2 - ζ| ≤ τ} with hE₂
  have hWm : Measurable fun p : ℝ × ℝ => W.toFun p.1 p.2 := W.measurable_uncurry
  have hE₁m : MeasurableSet E₁ :=
    (measurable_fst hG₁m).inter ((measurable_snd hG₁m).inter
      (measurableSet_le (hWm.sub measurable_const).abs measurable_const))
  have hE₂m : MeasurableSet E₂ :=
    (((measurable_fst hG₂m).inter (measurable_snd hG₁m)).union
      ((measurable_snd hG₂m).inter (measurable_fst hG₁m))).inter
      (measurableSet_le (hWm.sub measurable_const).abs measurable_const)
  have hE₁s : ∀ x y, (x, y) ∈ E₁ ↔ (y, x) ∈ E₁ := by
    intro x y
    simp only [hE₁, Set.mem_ofPred_eq, W.symm' x y]
    tauto
  have hE₂s : ∀ x y, (x, y) ∈ E₂ ↔ (y, x) ∈ E₂ := by
    intro x y
    simp only [hE₂, Set.mem_ofPred_eq, W.symm' x y]
    tauto
  -- the measure of `G₁`
  have hG₁c : (unitμ G₁ᶜ).toReal ≤ Q₁ / ω := by
    have h := unitμ_markov (W.measurable_rowDist ε) (W.rowDist_nonneg ε) (W.rowDist_le_one hε) hω
    rw [W.integral_rowDist] at h
    have hset : G₁ᶜ = {x | ω < W.rowDist ε x} := by ext x; simp [hG₁, not_le]
    rw [hset]; exact h
  have hG₁meas : 1 / 2 ≤ (unitμ G₁).toReal := by
    have h1 : (unitμ G₁).toReal + (unitμ G₁ᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
        measure_add_measure_compl hG₁m]
      simp
    linarith
  -- the measure of `G₂`
  have hIG₂ : (unitμ (I \ G₂)).toReal ≤ iI / 2 := by
    have hset : I \ G₂ = {x | ω < I.indicator (fun _ => (1:ℝ)) x * W.crossRowDist ε ζ I x} := by
      ext x
      simp only [hG₂, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and, not_le]
      constructor
      · rintro ⟨hxI, hx⟩
        rw [Set.indicator_of_mem hxI, one_mul]; exact hx hxI
      · intro hx
        by_cases hxI : x ∈ I
        · rw [Set.indicator_of_mem hxI, one_mul] at hx; exact ⟨hxI, fun _ => hx⟩
        · rw [Set.indicator_of_notMem hxI, zero_mul] at hx; exact absurd hx (not_lt.mpr hω.le)
    have hmeas : Measurable fun x => I.indicator (fun _ => (1:ℝ)) x * W.crossRowDist ε ζ I x :=
      (measurable_const.indicator hI).mul (W.measurable_crossRowDist ε ζ hI)
    have hnn : ∀ x, 0 ≤ I.indicator (fun _ => (1:ℝ)) x * W.crossRowDist ε ζ I x := fun x =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) x) (W.crossRowDist_nonneg ε ζ I x)
    have hle1 : ∀ x, I.indicator (fun _ => (1:ℝ)) x * W.crossRowDist ε ζ I x ≤ 1 := fun x => by
      have h1 := W.crossRowDist_le_one hε hζ I x
      have h2 := W.crossRowDist_nonneg ε ζ I x
      by_cases hxI : x ∈ I
      · rw [Set.indicator_of_mem hxI, one_mul]; exact h1
      · rw [Set.indicator_of_notMem hxI, zero_mul]; exact zero_le_one
    have h := unitμ_markov hmeas hnn hle1 hω
    have hint := W.integral_indicator_crossRowDist_le hε hζ hI
    rw [hset]
    calc _ ≤ (∫ x, I.indicator (fun _ => (1:ℝ)) x * W.crossRowDist ε ζ I x ∂unitμ) / ω := h
      _ ≤ Real.sqrt iI * Real.sqrt (∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2 ∂gμ)
            / ω := div_le_div_of_nonneg_right hint hω.le
      _ ≤ iI / 2 := hrω
  have hG₂meas : iI / 2 ≤ (unitμ G₂).toReal := by
    have hsub : G₂ ⊆ I := Set.inter_subset_left
    have h1 : (unitμ G₂).toReal + (unitμ (I \ G₂)).toReal = iI := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
        measure_add_sdiff hG₂m.nullMeasurableSet I, Set.union_eq_self_of_subset_left hsub]
    linarith
  -- `E₁` has positive measure
  have hE₁pos : 0 < (gμ E₁).toReal := by
    have hcover : G₁ ×ˢ G₁ ⊆ E₁ ∪ {p | τ < |W.toFun p.1 p.2 - ε|} := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      by_cases h : |W.toFun x y - ε| ≤ τ
      · exact Or.inl ⟨hx, hy, h⟩
      · exact Or.inr (not_le.mp h)
    have hm1 := measure_mono (μ := gμ) hcover
    have hm2 := le_trans hm1 (measure_union_le _ _)
    have hreal := ENNReal.toReal_mono (by simp [measure_ne_top]) hm2
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
    have hprod : (gμ (G₁ ×ˢ G₁)).toReal = (unitμ G₁).toReal ^ 2 := by
      unfold gμ; rw [Measure.prod_prod, ENNReal.toReal_mul]; ring
    have hbad : (gμ {p : ℝ × ℝ | τ < |W.toFun p.1 p.2 - ε|}).toReal ≤ 1 / 8 := by
      have h := gμ_markov (f := fun p : ℝ × ℝ => |W.toFun p.1 p.2 - ε|)
        ((hWm.sub measurable_const).abs) (fun _ => abs_nonneg _)
        (C := 1) (fun p => by
          have := W.mem_Icc p.1 p.2
          rw [abs_le]; constructor <;> linarith [this.1, this.2, hε.1, hε.2]) hτ
      exact le_trans h hQτ
    have hsq : 1 / 4 ≤ (unitμ G₁).toReal ^ 2 := by nlinarith
    linarith
  -- `E₂` has positive measure
  have hE₂pos : 0 < (gμ E₂).toReal := by
    set r2 : ℝ := ∫ p : ℝ × ℝ, (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2 ∂gμ with hr2
    have hcover : G₂ ×ˢ G₁ ⊆ E₂ ∪ ({p | τ ^ 2 < (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2}
        ∪ I ×ˢ I) := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      by_cases h : |W.toFun x y - ζ| ≤ τ
      · exact Or.inl ⟨Or.inl ⟨hx, hy⟩, h⟩
      · by_cases hyI : y ∈ I
        · exact Or.inr (Or.inr ⟨hx.1, hyI⟩)
        · refine Or.inr (Or.inl ?_)
          have hW0 : crossProfile ε ζ I (x, y) = ζ := by
            have hmem : (x, y) ∈ crossSet I := Or.inl ⟨hx.1, hyI⟩
            unfold crossProfile
            rw [Set.indicator_of_mem hmem]; ring
          show τ ^ 2 < (W.toFun x y - crossProfile ε ζ I (x, y)) ^ 2
          rw [hW0, ← sq_abs (W.toFun x y - ζ)]
          exact pow_lt_pow_left₀ (not_le.mp h) hτ.le (by norm_num : (2:ℕ) ≠ 0)
    have hm1 := measure_mono (μ := gμ) hcover
    have hm2 := le_trans hm1 (le_trans (measure_union_le _ _)
      (add_le_add le_rfl (measure_union_le _ _)))
    have hreal := ENNReal.toReal_mono (by simp [measure_ne_top]) hm2
    rw [ENNReal.toReal_add (measure_ne_top _ _) (by simp [measure_ne_top]),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
    have hprod : (gμ (G₂ ×ˢ G₁)).toReal = (unitμ G₂).toReal * (unitμ G₁).toReal := by
      unfold gμ; rw [Measure.prod_prod, ENNReal.toReal_mul]
    have hII : (gμ (I ×ˢ I)).toReal = iI ^ 2 := by
      unfold gμ; rw [Measure.prod_prod, ENNReal.toReal_mul]; ring
    have hbad : (gμ {p : ℝ × ℝ | τ ^ 2 < (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2}).toReal
        ≤ iI / 16 := by
      have h := gμ_markov (f := fun p : ℝ × ℝ => (W.toFun p.1 p.2 - crossProfile ε ζ I p) ^ 2)
        ((hWm.sub (measurable_crossProfile ε ζ hI)).pow_const 2) (fun _ => sq_nonneg _) (C := 1)
        (fun p => by
          have h1 := W.mem_Icc p.1 p.2
          have h2 := crossProfile_mem_Icc hε hζ I p
          nlinarith [h1.1, h1.2, h2.1, h2.2]) (by positivity : 0 < τ ^ 2)
      exact le_trans h hrτ
    have h1 : iI / 2 * (1 / 2) ≤ (unitμ G₂).toReal * (unitμ G₁).toReal :=
      mul_le_mul hG₂meas hG₁meas (by norm_num) ENNReal.toReal_nonneg
    have h2 : iI ^ 2 ≤ iI / 16 := by nlinarith
    rw [hprod, hII] at hreal
    linarith
  refine ⟨E₁, E₂, hE₁m, hE₂m, hE₁s, hE₂s, hE₁pos, hE₂pos, fun p hp => hp.2.2, fun p hp => hp.2, ?_, ?_⟩
  · intro p hp
    obtain ⟨hx, hy, -⟩ := hp
    have h1 := W.abs_gammaW_sub_row_le H hreg hε p.1 p.2
    have h2 : W.rowDist ε p.2 ≤ ω := hy
    have hdx : |W.degFun p.1 - ε| ≤ ω := le_trans (W.abs_degFun_sub_le_rowDist ε p.1) hx
    have h3 : |W.degFun p.1 ^ (d - 1) - ε ^ (d - 1)| ≤ ((d : ℝ) - 1) * ω :=
      le_trans (abs_pow_pred_sub_le (by omega) (W.degFun_mem_Icc p.1) hε)
        (mul_le_mul_of_nonneg_left hdx hd1)
    have hεpow : ε ^ (H.edgeFinset.card - d) ≤ 1 := pow_le_one₀ hε.1 hε.2
    have hεpow0 : 0 ≤ ε ^ (H.edgeFinset.card - d) := pow_nonneg hε.1 _
    have h4 : |mR * (ε ^ (H.edgeFinset.card - d) * W.degFun p.1 ^ (d - 1))
        - mR * (ε ^ (H.edgeFinset.card - d) * ε ^ (d - 1))| ≤ mR * ((d : ℝ) - 1) * ω := by
      rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg hmR0, abs_of_nonneg hεpow0]
      calc mR * (ε ^ (H.edgeFinset.card - d) * |W.degFun p.1 ^ (d - 1) - ε ^ (d - 1)|)
          ≤ mR * (1 * (((d : ℝ) - 1) * ω)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hεpow h3 (abs_nonneg _) zero_le_one) hmR0
        _ = mR * ((d : ℝ) - 1) * ω := by ring
    have h5 : mR * (mR * (W.rowDist ε p.2 + Q₁)) ≤ mR * (mR * (ω + Q₁)) := by
      apply mul_le_mul_of_nonneg_left _ hmR0
      apply mul_le_mul_of_nonneg_left _ hmR0
      linarith
    have h6 : mR * ((d : ℝ) - 1) * ω ≤ mR * ((d : ℝ) - 1) * (ω + iI) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hmR0 hd1)
      linarith [ENNReal.toReal_nonneg (a := unitμ I)]
    calc |W.gammaW H p.1 p.2 - mR * (ε ^ (H.edgeFinset.card - d) * ε ^ (d - 1))|
        ≤ |W.gammaW H p.1 p.2 - mR * (ε ^ (H.edgeFinset.card - d) * W.degFun p.1 ^ (d - 1))|
          + |mR * (ε ^ (H.edgeFinset.card - d) * W.degFun p.1 ^ (d - 1))
            - mR * (ε ^ (H.edgeFinset.card - d) * ε ^ (d - 1))| := abs_sub_le _ _ _
      _ ≤ mR * (mR * (W.rowDist ε p.2 + Q₁)) + mR * ((d : ℝ) - 1) * ω := add_le_add h1 h4
      _ ≤ mR * (mR * (ω + Q₁)) + mR * ((d : ℝ) - 1) * (ω + iI) := add_le_add h5 h6
  · -- the `ζ`-region, using the symmetry of `Γ_W`
    have hkey : ∀ x y, x ∈ G₂ → y ∈ G₁ →
        |W.gammaW H x y - mR * (ε ^ (H.edgeFinset.card - d) * ζ ^ (d - 1))|
          ≤ mR * (mR * (ω + Q₁)) + mR * ((d : ℝ) - 1) * (ω + iI) := by
      intro x y hx hy
      have h1 := W.abs_gammaW_sub_row_le H hreg hε x y
      have h2 : W.rowDist ε y ≤ ω := hy
      have hx2 : W.crossRowDist ε ζ I x ≤ ω := hx.2
      have hdx : |W.degFun x - ζ| ≤ ω + iI :=
        le_trans (W.abs_degFun_sub_zeta_le hε hζ hI hx.1) (by linarith)
      have h3 : |W.degFun x ^ (d - 1) - ζ ^ (d - 1)| ≤ ((d : ℝ) - 1) * (ω + iI) :=
        le_trans (abs_pow_pred_sub_le (by omega) (W.degFun_mem_Icc x) hζ)
          (mul_le_mul_of_nonneg_left hdx hd1)
      have hεpow : ε ^ (H.edgeFinset.card - d) ≤ 1 := pow_le_one₀ hε.1 hε.2
      have hεpow0 : 0 ≤ ε ^ (H.edgeFinset.card - d) := pow_nonneg hε.1 _
      have h4 : |mR * (ε ^ (H.edgeFinset.card - d) * W.degFun x ^ (d - 1))
          - mR * (ε ^ (H.edgeFinset.card - d) * ζ ^ (d - 1))| ≤ mR * ((d : ℝ) - 1) * (ω + iI) := by
        rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg hmR0, abs_of_nonneg hεpow0]
        calc mR * (ε ^ (H.edgeFinset.card - d) * |W.degFun x ^ (d - 1) - ζ ^ (d - 1)|)
            ≤ mR * (1 * (((d : ℝ) - 1) * (ω + iI))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hεpow h3 (abs_nonneg _) zero_le_one) hmR0
          _ = mR * ((d : ℝ) - 1) * (ω + iI) := by ring
      have h5 : mR * (mR * (W.rowDist ε y + Q₁)) ≤ mR * (mR * (ω + Q₁)) := by
        apply mul_le_mul_of_nonneg_left _ hmR0
        apply mul_le_mul_of_nonneg_left _ hmR0
        linarith
      calc |W.gammaW H x y - mR * (ε ^ (H.edgeFinset.card - d) * ζ ^ (d - 1))|
          ≤ |W.gammaW H x y - mR * (ε ^ (H.edgeFinset.card - d) * W.degFun x ^ (d - 1))|
            + |mR * (ε ^ (H.edgeFinset.card - d) * W.degFun x ^ (d - 1))
              - mR * (ε ^ (H.edgeFinset.card - d) * ζ ^ (d - 1))| := abs_sub_le _ _ _
        _ ≤ mR * (mR * (W.rowDist ε y + Q₁)) + mR * ((d : ℝ) - 1) * (ω + iI) := add_le_add h1 h4
        _ ≤ mR * (mR * (ω + Q₁)) + mR * ((d : ℝ) - 1) * (ω + iI) := add_le_add h5 le_rfl
    intro p hp
    rcases hp.1 with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact hkey p.1 p.2 hx hy
    · rw [W.gammaW_symm H p.1 p.2]; exact hkey p.2 p.1 hy hx

end Graphon

end UpperTailOptimizers
