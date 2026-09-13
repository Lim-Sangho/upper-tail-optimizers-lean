import UpperTailOptimizers.SingularEndpoint.JpConvexGap
import UpperTailOptimizers.KRRS.Reduced

/-!
# Strong concavity of the entropy at fixed edge density

`S₀'' = -1/(2u(1-u)) ≤ -2`, so `S₀(u) ≤ S₀(v) + S₀'(v)(u-v) - (u-v)²`.  Integrated against a
graphon of edge density `ε`, the linear term vanishes:

  `s(W) ≤ S₀(ε) - ‖W - ε‖₂²`.

This is `kb:eq:strong-concavity` of the bipodality draft, the first half of its localization
lemma.
-/

namespace UpperTailOptimizers

open MeasureTheory Real

theorem S0_le_tangent_sub_sq {u v : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) (hv0 : 0 < v) (hv1 : v < 1) :
    S0 u ≤ S0 v + dS0 v * (u - v) - (u - v) ^ 2 := by
  have h := SingularEndpoint.two_sq_le_Jp_convexGap (p := 1 / 2) (by norm_num) (by norm_num)
    hu hv0 hv1
  have hJ : ∀ w ∈ Set.Icc (0:ℝ) 1, Jp (1 / 2) w = -2 * S0 w + Real.log 2 := by
    intro w hw
    unfold Jp S0 shannonH entIntegrand
    rcases eq_or_lt_of_le hw.1 with h0 | h0
    · subst h0
      simp only [zero_mul, zero_add, sub_zero, one_mul, zero_div, Real.log_zero]
      rw [show (1:ℝ) / (1 - 1 / 2) = 2 by norm_num]
      simp
    rcases eq_or_lt_of_le hw.2 with h1 | h1
    · subst h1
      simp only [sub_self, add_zero, one_mul, zero_div, Real.log_zero, mul_zero]
      rw [show (1:ℝ) / (1 / 2) = 2 by norm_num]
      simp
    · have h1w : (0:ℝ) < 1 - w := by linarith
      rw [Real.log_div (ne_of_gt h0) (by norm_num), Real.log_div (ne_of_gt h1w) (by norm_num),
        show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num, show (1:ℝ) / 2 = (2:ℝ)⁻¹ by norm_num,
        Real.log_inv]
      ring
  have hJ' : Jp' (1 / 2) v = -2 * dS0 v := by
    unfold Jp' dS0
    have h1v : (0:ℝ) < 1 - v := by linarith
    rw [show v * (1 - 1 / 2) / ((1 - v) * (1 / 2)) = v / (1 - v) by field_simp; norm_num,
      Real.log_div (ne_of_gt hv0) (ne_of_gt h1v)]
    ring
  rw [hJ u hu, hJ v ⟨hv0.le, hv1.le⟩, hJ'] at h
  nlinarith [h]

/-- The graphon entropy is the integral of `S₀`. -/
theorem Graphon.entropy_eq_integral_S0 (W : Graphon) :
    W.entropy = ∫ z, S0 (W.toFun z.1 z.2) ∂gμ := by
  unfold Graphon.entropy S0 shannonH entIntegrand
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

/-- **Strong concavity at fixed edge density.** -/
theorem Graphon.entropy_le_S0_sub_sq (W : Graphon) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (he : W.edgeDensity = ε) :
    W.entropy ≤ S0 ε - ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ := by
  have hS0c : ContinuousOn S0 (Set.Icc 0 1) := by
    have : Continuous S0 := by
      have h : S0 = fun u => Real.binEntropy u / 2 := by
        funext u; unfold S0; rw [shannonH_eq_binEntropy]
      rw [h]; exact Real.binEntropy_continuous.div_const 2
    exact this.continuousOn
  have hS0m : Measurable S0 := by
    have h : S0 = fun u => Real.binEntropy u / 2 := by
      funext u; unfold S0; rw [shannonH_eq_binEntropy]
    rw [h]; exact (Real.binEntropy_continuous.div_const 2).measurable
  have hI1 : Integrable (fun z : ℝ × ℝ => S0 (W.toFun z.1 z.2)) gμ :=
    W.integrable_comp hS0m hS0c
  have hsq : Integrable (fun z : ℝ × ℝ => (W.toFun z.1 z.2 - ε) ^ 2) gμ :=
    W.integrable_comp (g := fun t => (t - ε) ^ 2) (by fun_prop) (by fun_prop)
  have hlin : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2 - ε) gμ :=
    W.integrable_comp (g := fun t => t - ε) (by fun_prop) (by fun_prop)
  have hbound : ∀ z : ℝ × ℝ, S0 (W.toFun z.1 z.2)
      ≤ S0 ε + dS0 ε * (W.toFun z.1 z.2 - ε) - (W.toFun z.1 z.2 - ε) ^ 2 :=
    fun z => S0_le_tangent_sub_sq (W.mem_Icc z.1 z.2) hε0 hε1
  have hint : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2) gμ :=
    W.integrable_comp (g := fun t => t) measurable_id continuousOn_id
  have hlin0 : ∫ z, (W.toFun z.1 z.2 - ε) ∂gμ = 0 := by
    rw [integral_sub hint (integrable_const ε), integral_const]
    have h' : ∫ z, W.toFun z.1 z.2 ∂gμ = ε := he
    simp [h']
  have hrhs : ∫ z, (S0 ε + dS0 ε * (W.toFun z.1 z.2 - ε) - (W.toFun z.1 z.2 - ε) ^ 2) ∂gμ
      = S0 ε - ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ := by
    have hB : Integrable (fun z : ℝ × ℝ => dS0 ε * (W.toFun z.1 z.2 - ε)) gμ :=
      hlin.const_mul _
    have hA : Integrable (fun z : ℝ × ℝ => S0 ε + dS0 ε * (W.toFun z.1 z.2 - ε)) gμ :=
      (integrable_const _).add hB
    rw [integral_sub hA hsq, integral_add (integrable_const _) hB, integral_const_mul, hlin0,
      integral_const]
    simp
  calc W.entropy = ∫ z, S0 (W.toFun z.1 z.2) ∂gμ := W.entropy_eq_integral_S0
    _ ≤ ∫ z, (S0 ε + dS0 ε * (W.toFun z.1 z.2 - ε) - (W.toFun z.1 z.2 - ε) ^ 2) ∂gμ :=
        integral_mono hI1 (((integrable_const _).add (hlin.const_mul _)).sub hsq) hbound
    _ = _ := hrhs

end UpperTailOptimizers
