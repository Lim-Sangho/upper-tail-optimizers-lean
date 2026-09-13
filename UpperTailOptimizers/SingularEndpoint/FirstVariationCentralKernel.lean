import UpperTailOptimizers.SingularEndpoint.DistributionWindow
import UpperTailOptimizers.SingularEndpoint.ContinuationKernelBounds

/-!
# `lem:first-variation-bound` and `lem:central-kernel-bound` in the form of the paper

`sec:auxiliary-lagrangian` (`paper/sections/singular_auxiliary_lagrangian.tex`) uses the **open**
central neighbourhood `𝒩_ρ = (u_* - ρ, u_* + ρ)` and the **closed** tail
`𝒯_ρ = [0,2] ∖ 𝒩_ρ` (`openWindow`).  The Lean window estimates use the closed window
`centralWindow d ρ = [u_* - ρ, u_* + ρ]`, whose tail misses the two boundary points.  For a
measure with atoms at `u_* ± ρ` the two versions of `A_{h,ρ}` and of the tail mass differ, so
neither inequality implies the other.  This file states the two lemmas with the paper's sets
and quantifiers.

* **`lem:first-variation-bound`** (`first_variation_bound`): there are `ρ₀ > 0` and
  `a = d³/24` such that for every `0 < ρ < ρ₀` there are `b_ρ, h_ρ > 0` with
  `Ψ_h ≥ aQ_h²` on `𝒩_ρ` and `Ψ_h ≥ b_ρ` on `𝒯_ρ` for `0 < h < h_ρ`.  Here `Ψ_h` is the
  continued potential `KKTFamily.PsiT`, i.e. `2∫K_h(x,y)dν_h(y) - (2γ_hq_h/d)x^d - κ_h` with
  `Ψ_h(s_h) = 0` (`PsiT_eq_integral`, `PsiT_sVal`).  The closed-window bound
  `exists_firstVariation_lower_PsiT` restricts to `𝒩_ρ`, and `exists_firstVariation_upperGap`
  is already stated on `{x ∈ [0,2] : |x - u_*| ≥ ρ} = 𝒯_ρ`.
* **`lem:central-kernel-bound`** (`central_kernel_bound`): with the same `a`, there are `ρ₀ > 0`
  and `C ≥ 1` such that for every `0 < ρ < ρ₀` there is `h_ρ > 0` with, for `0 < h < h_ρ` and
  every probability measure `ξ` on `[0,2]`,
  `∬_{𝒩_ρ²} K_h dσ dσ ≥ -(a/2)A_{h,ρ}(ξ) - C{Δ_h(ξ)² + ξ(𝒯_ρ)²}`, `σ = ξ - ν_h`.
  The double integral is the iterated `σ`-integral `sigmaInt` (the development never forms
  signed measures).  `C` is independent of `ρ`.

## The proof of `central_kernel_bound`

The closed-window bound `centralQuad_lower` is applied, at a **fixed** radius `ρ_*` from
`exists_distribution_window`, to the transported measure

`ξ' = ξ|_{𝒩_ρ} + ξ(𝒩_ρᶜ)·δ_0`   (`tailToZero`),   `0 < ρ < ρ_*`.

Because `𝒩_ρ ⊆ [u_* - ρ_*, u_* + ρ_*] = W` and `0 ∉ W`, the restriction of `ξ'` to `W` is the
restriction of `ξ` to `𝒩_ρ`: the closed-window quadratic form, `A` and the tail mass of `ξ'`
at radius `ρ_*` are the open-window quantities of `ξ` at radius `ρ`, and the moment changes by
at most `2^d ξ(𝒯_ρ)`.  All constants come from the window package at `ρ_*`, so they do not
depend on `ρ`; only the threshold `h_ρ` (both atoms in `𝒩_ρ`) does.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-- The paper's **open** central neighbourhood `𝒩_ρ = (u_* - ρ, u_* + ρ)`; the tail is
`𝒯_ρ = [0,2] ∖ 𝒩_ρ`. -/
def openWindow (d : ℕ) (ρ : ℝ) : Set ℝ := Set.Ioo (uStar d - ρ) (uStar d + ρ)

theorem measurableSet_openWindow (d : ℕ) (ρ : ℝ) : MeasurableSet (openWindow d ρ) :=
  measurableSet_Ioo

namespace KKTFamily

/-- **`eq:first-variation`**: `Ψ_h(x) = 2∫K_h(x,y)dν_h(y) - (2γ_hq_h/d)x^d - κ_h`. -/
theorem PsiT_eq_integral (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) (x : ℝ) :
    B.PsiT h x
      = 2 * ∫ y, B.contKernel h x y ∂(B.distributionMeasure h) - B.etaVal h * x ^ d
        - B.kappaVal h := by
  have h1 := integral_distributionMeasure_kernel B hh x
  simp only [contKernel]
  rw [h1, PsiT, crossK]

end KKTFamily

/-! ## `lem:first-variation-bound` -/

/-- **`lem:first-variation-bound`.**  With `a = d³/24`: there is `ρ₀ > 0` such that for every
`0 < ρ < ρ₀` there are `b_ρ > 0` and `0 < h_ρ ≤ h₀` with, for all `0 < h < h_ρ`,
`Ψ_h(x) ≥ aQ_h(x)²` on `𝒩_ρ` and `Ψ_h(x) ≥ b_ρ` on `𝒯_ρ`. -/
theorem first_variation_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      ∃ b hρ : ℝ, 0 < b ∧ 0 < hρ ∧ hρ ≤ B.h₀ ∧ ∀ h : ℝ, 0 < h → h < hρ →
        (∀ x ∈ openWindow d ρ, (d : ℝ) ^ 3 / 24 * B.Qh h x ^ 2 ≤ B.PsiT h x) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 2 \ openWindow d ρ, b ≤ B.PsiT h x) := by
  obtain ⟨w, hw, δ₁, hδ₁, hlow⟩ := KKTFamily.exists_firstVariation_lower_PsiT hd B
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  refine ⟨min w (min (uStar d / 2) ((1 - uStar d) / 2)),
    lt_min hw (lt_min (by linarith) (by linarith)), fun ρ hρ0 hρlt => ?_⟩
  have hρw : ρ ≤ w := le_trans hρlt.le (min_le_left _ _)
  have hρu : ρ ≤ uStar d / 2 := le_trans hρlt.le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ1 : ρ ≤ (1 - uStar d) / 2 :=
    le_trans hρlt.le (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨b, hb, δ₂, hδ₂, hgap⟩ := KKTFamily.exists_firstVariation_upperGap hd B hρ0
  refine ⟨b, min (min δ₁ δ₂) B.h₀, hb, lt_min (lt_min hδ₁ hδ₂) B.h₀_pos, min_le_right _ _,
    fun h hh0 hhlt => ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
  · have hhδ₁ : h < δ₁ := lt_of_lt_of_le hhlt (le_trans (min_le_left _ _) (min_le_left _ _))
    have hhB : |h| < B.h₀ := by
      rw [abs_of_pos hh0]; exact lt_of_lt_of_le hhlt (min_le_right _ _)
    exact hlow h hh0 hhδ₁ hhB ρ hρw hρu hρ1 x (Set.Ioo_subset_Icc_self hx)
  · have hhδ₂ : |h| < δ₂ := by
      rw [abs_of_pos hh0]
      exact lt_of_lt_of_le hhlt (le_trans (min_le_left _ _) (min_le_right _ _))
    have hhB : |h| < B.h₀ := by
      rw [abs_of_pos hh0]; exact lt_of_lt_of_le hhlt (min_le_right _ _)
    have hρx : ρ ≤ |x - uStar d| := by
      by_contra hcon
      obtain ⟨h1, h2⟩ := abs_lt.mp (not_le.mp hcon)
      exact hx.2 ⟨by linarith, by linarith⟩
    exact hgap h hhδ₂ hhB x hx.1 hρx

/-! ## Moving the tail mass to the origin -/

/-- `ξ|_S + ξ(Sᶜ)·δ_0`. -/
noncomputable def tailToZero (ξ : Measure ℝ) (S : Set ℝ) : Measure ℝ :=
  ξ.restrict S + ξ Sᶜ • Measure.dirac 0

theorem isProbabilityMeasure_tailToZero {ξ : Measure ℝ} [IsProbabilityMeasure ξ] {S : Set ℝ}
    (hS : MeasurableSet S) : IsProbabilityMeasure (tailToZero ξ S) := by
  constructor
  rw [tailToZero, Measure.add_apply, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.dirac_apply_of_mem (Set.mem_univ 0), smul_eq_mul, mul_one,
    measure_add_measure_compl hS, measure_univ]

theorem tailToZero_Icc_compl {ξ : Measure ℝ} (hξ : ξ (Set.Icc (0 : ℝ) 2)ᶜ = 0) (S : Set ℝ) :
    tailToZero ξ S (Set.Icc (0 : ℝ) 2)ᶜ = 0 := by
  have hm : MeasurableSet (Set.Icc (0 : ℝ) 2)ᶜ := measurableSet_Icc.compl
  rw [tailToZero, Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hm,
    Measure.dirac_apply' 0 hm, Set.indicator_of_notMem (by simp), smul_zero, add_zero]
  exact measure_mono_null Set.inter_subset_left hξ

theorem restrict_tailToZero (ξ : Measure ℝ) {S W : Set ℝ} (hW : MeasurableSet W) (hSW : S ⊆ W)
    (h0 : (0 : ℝ) ∉ W) : (tailToZero ξ S).restrict W = ξ.restrict S := by
  classical
  rw [tailToZero, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_restrict hW,
    Set.inter_eq_right.mpr hSW, restrict_dirac, if_neg h0, smul_zero, add_zero]

theorem tailToZero_tail {ξ : Measure ℝ} (hξ : ξ (Set.Icc (0 : ℝ) 2)ᶜ = 0) {S W : Set ℝ}
    (hW : MeasurableSet W) (hSW : S ⊆ W) (h0 : (0 : ℝ) ∉ W) :
    tailToZero ξ S (Set.Icc (0 : ℝ) 2 \ W) = ξ (Set.Icc (0 : ℝ) 2 \ S) := by
  have hm : MeasurableSet (Set.Icc (0 : ℝ) 2 \ W) := measurableSet_Icc.diff hW
  have hempty : (Set.Icc (0 : ℝ) 2 \ W) ∩ S = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxS
    exact hx.2 (hSW hxS)
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 2 \ W := ⟨⟨le_rfl, by norm_num⟩, h0⟩
  have hdiff : Sᶜ \ (Set.Icc (0 : ℝ) 2)ᶜ = Set.Icc (0 : ℝ) 2 \ S := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_compl_iff, not_not]
    exact and_comm
  rw [tailToZero, Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hm, hempty,
    measure_empty, zero_add, Measure.dirac_apply_of_mem h0mem, smul_eq_mul, mul_one, ← hdiff,
    measure_sdiff_null hξ]

/-! ## `lem:central-kernel-bound` -/

set_option maxHeartbeats 1600000 in
/-- **`lem:central-kernel-bound`.**  With `a = d³/24` (the constant of
`first_variation_bound`): there are `ρ₀ > 0` and `C ≥ 1` such that for every `0 < ρ < ρ₀`
there is `0 < h_ρ ≤ h₀` with, for all `0 < h < h_ρ` and every probability measure `ξ` on
`[0,2]`,

`∬_{𝒩_ρ²} K_h dσ dσ ≥ -(a/2) A_{h,ρ}(ξ) - C {Δ_h(ξ)² + ξ(𝒯_ρ)²}`,   `σ = ξ - ν_h`,

where `A_{h,ρ}(ξ) = ∫_{𝒩_ρ} Q_h² dξ` and `Δ_h(ξ) = ∫x^d dξ - q_h`.  `C` does not depend on `ρ`. -/
theorem central_kernel_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ₀ C : ℝ, 0 < ρ₀ ∧ 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧ ∀ h : ℝ, 0 < h → h < hρ →
        ∀ ξ : Measure ℝ, IsProbabilityMeasure ξ → ξ (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          -((d : ℝ) ^ 3 / 24 / 2) * (∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂ξ)
            - C * (((∫ x, x ^ d ∂ξ) - B.qVal h) ^ 2
                + (ξ (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal ^ 2)
          ≤ B.sigmaInt h ξ (openWindow d ρ)
              (fun x => B.sigmaInt h ξ (openWindow d ρ) (fun y => B.contKernel h x y)) := by
  classical
  obtain ⟨ρs, hρs, Cu, hCu, Cp, hCp, C₀, -, hth, hthpos, hρu, hρ1, hwin⟩ :=
    KKTFamily.exists_distribution_window hd B
  have hdR : (0 : ℝ) < (d : ℝ) := dpos hd
  have hd3 : (0 : ℝ) < (d : ℝ) ^ 3 := by positivity
  obtain ⟨Mc, hMc⟩ : ∃ Mc : ℝ, Mc = Cp + 192 * Cu ^ 2 / (d : ℝ) ^ 3 := ⟨_, rfl⟩
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 1 + 2 * 2 ^ d := ⟨_, rfl⟩
  have hK₁1 : 1 ≤ K₁ := by
    have h2 : (0 : ℝ) ≤ 2 ^ d := by positivity
    rw [hK₁]
    linarith
  have hu0 : 0 < uStar d := uStar_pos hd
  refine ⟨ρs, 1 + 2 * Mc * K₁ ^ 2, hρs, by nlinarith [mul_nonneg hMc0 (sq_nonneg K₁)],
    fun ρ hρ0 hρlt => ?_⟩
  obtain ⟨δa, hδa, hatoms⟩ := B.exists_atoms_mem_centralWindow (half_pos hρ0)
  refine ⟨min (min hth δa) B.h₀, lt_min (lt_min hthpos hδa) B.h₀_pos, min_le_right _ _, ?_⟩
  intro h hpos hlt ξ hξprob hξ
  have hhth : h < hth := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhδa : h < δa := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhB : |h| < B.h₀ := by rw [abs_of_pos hpos]; exact lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨hsρ2, htρ2⟩ := hatoms h hpos hhδa
  have hw := hwin h hpos hhth hhB
  -- the open window sits inside the fixed closed window, which misses the origin
  have hSmeas : MeasurableSet (openWindow d ρ) := measurableSet_openWindow d ρ
  have hWmeas : MeasurableSet (centralWindow d ρs) := measurableSet_centralWindow d ρs
  have hSW : openWindow d ρ ⊆ centralWindow d ρs := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h0W : (0 : ℝ) ∉ centralWindow d ρs := fun hx => by
    have h1 : uStar d - ρs ≤ 0 := hx.1
    linarith
  have hsS : B.sVal h ∈ openWindow d ρ := by
    have h1 : B.sVal h ∈ Set.Icc (uStar d - ρ / 2) (uStar d + ρ / 2) := hsρ2
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have htS : B.tVal h ∈ openWindow d ρ := by
    have h1 : B.tVal h ∈ Set.Icc (uStar d - ρ / 2) (uStar d + ρ / 2) := htρ2
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  -- the transported measure
  have hν' : IsProbabilityMeasure (tailToZero ξ (openWindow d ρ)) :=
    isProbabilityMeasure_tailToZero hSmeas
  have hν'supp := tailToZero_Icc_compl hξ (openWindow d ρ)
  have hrestr := restrict_tailToZero ξ hWmeas hSW h0W
  have hdistW : (B.distributionMeasure h).restrict (centralWindow d ρs) = B.distributionMeasure h :=
    B.distributionMeasure_restrict_of_mem (hSW hsS) (hSW htS)
  have hdistS : (B.distributionMeasure h).restrict (openWindow d ρ) = B.distributionMeasure h :=
    B.distributionMeasure_restrict_of_mem hsS htS
  have hquad : B.centralQuad h ρs (tailToZero ξ (openWindow d ρ))
      = B.sigmaInt h ξ (openWindow d ρ)
          (fun x => B.sigmaInt h ξ (openWindow d ρ) (fun y => B.contKernel h x y)) := by
    simp only [KKTFamily.centralQuad, KKTFamily.innerSigma, KKTFamily.sigmaInt,
      KKTFamily.contKernel]
    rw [hrestr, hdistW, hdistS]
  have hA : ∫ x in centralWindow d ρs, B.Qh h x ^ 2 ∂(tailToZero ξ (openWindow d ρ))
      = ∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂ξ := by rw [hrestr]
  have hT : tailToZero ξ (openWindow d ρ) (Set.Icc (0 : ℝ) 2 \ centralWindow d ρs)
      = ξ (Set.Icc (0 : ℝ) 2 \ openWindow d ρ) := tailToZero_tail hξ hWmeas hSW h0W
  -- the moment of the transported measure
  have hint : Integrable (fun x : ℝ => x ^ d) ξ := integrable_of_continuousOn hξ (by fun_prop)
  have hmom' : ∫ x, x ^ d ∂(tailToZero ξ (openWindow d ρ)) = ∫ x in openWindow d ρ, x ^ d ∂ξ := by
    have hi1 : Integrable (fun x : ℝ => x ^ d) (ξ.restrict (openWindow d ρ)) := hint.restrict
    have hi2 : Integrable (fun x : ℝ => x ^ d) (ξ (openWindow d ρ)ᶜ • Measure.dirac (0 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (measure_ne_top _ _)
    rw [tailToZero, integral_add_measure hi1 hi2, integral_smul_measure, integral_dirac,
      zero_pow (by omega : d ≠ 0), smul_zero, add_zero]
  have htailInt : |∫ x in (openWindow d ρ)ᶜ, x ^ d ∂ξ|
      ≤ 2 ^ d * (ξ (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal := by
    have heq : ∫ x in (openWindow d ρ)ᶜ, x ^ d ∂ξ
        = ∫ x in Set.Icc (0 : ℝ) 2 ∩ (openWindow d ρ)ᶜ, x ^ d ∂ξ := by
      rw [restrict_Icc_inter hξ]
    have hb : ∀ x ∈ Set.Icc (0 : ℝ) 2 ∩ (openWindow d ρ)ᶜ, ‖x ^ d‖ ≤ (2 : ℝ) ^ d := by
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1.1 d)]
      exact pow_le_pow_left₀ hx.1.1 hx.1.2 d
    have hn := norm_setIntegral_le_of_norm_le_const (μ := ξ) (measure_lt_top ξ _) hb
    rw [heq]
    simpa [Real.norm_eq_abs, measureReal_def, Set.sdiff_eq] using hn
  have hsplit : ∫ x, x ^ d ∂ξ
      = (∫ x in openWindow d ρ, x ^ d ∂ξ) + ∫ x in (openWindow d ρ)ᶜ, x ^ d ∂ξ :=
    (integral_add_compl hSmeas hint).symm
  -- the closed-window estimate for the transported measure
  have hlow := KKTFamily.centralQuad_lower hd B hhB hpos hρu hρ1
    (ν := tailToZero ξ (openWindow d ρ)) hν'supp hw.sVal_mem hw.tVal_mem
    (δ := (d : ℝ) ^ 3 / 192) (by positivity) hCu.le hCp.le hw.kp00_le hw.kpd0_le hw.kp0d_le
    hw.kpdd_le hw.u0_le hw.ud_le hw.tailSq_le
  rw [hA, hT, hmom', hquad, ← hMc] at hlow
  -- names for the scalars
  set A := ∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂ξ with hAdef
  set T := (ξ (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal with hTdef
  set Δ := (∫ x, x ^ d ∂ξ) - B.qVal h with hΔdef
  set Q := B.sigmaInt h ξ (openWindow d ρ)
    (fun x => B.sigmaInt h ξ (openWindow d ρ) (fun y => B.contKernel h x y)) with hQdef
  have hA0 : 0 ≤ A := setIntegral_nonneg hSmeas fun x _ => sq_nonneg _
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hΔ' : |(∫ x in openWindow d ρ, x ^ d ∂ξ) - B.qVal h| ≤ |Δ| + 2 ^ d * T := by
    have h1 : (∫ x in openWindow d ρ, x ^ d ∂ξ) - B.qVal h
        = Δ - ∫ x in (openWindow d ρ)ᶜ, x ^ d ∂ξ := by
      rw [hΔdef, hsplit]; ring
    rw [h1]
    exact le_trans (abs_sub _ _) (by linarith [htailInt])
  have hX0 : 0 ≤ (1 + 2 ^ d) * T + |(∫ x in openWindow d ρ, x ^ d ∂ξ) - B.qVal h| := by
    positivity
  have hXY : (1 + 2 ^ d) * T + |(∫ x in openWindow d ρ, x ^ d ∂ξ) - B.qVal h|
      ≤ K₁ * T + |Δ| := by
    rw [hK₁]; nlinarith [hΔ']
  have hsq : ((1 + 2 ^ d) * T + |(∫ x in openWindow d ρ, x ^ d ∂ξ) - B.qVal h|) ^ 2
      ≤ 2 * K₁ ^ 2 * T ^ 2 + 2 * Δ ^ 2 := by
    have h1 := pow_le_pow_left₀ hX0 hXY 2
    have h2 : (K₁ * T + |Δ|) ^ 2 ≤ 2 * K₁ ^ 2 * T ^ 2 + 2 * Δ ^ 2 := by
      have h3 : |Δ| ^ 2 = Δ ^ 2 := sq_abs Δ
      nlinarith [sq_nonneg (K₁ * T - |Δ|)]
    linarith
  have hMcsq : Mc * ((1 + 2 ^ d) * T + |(∫ x in openWindow d ρ, x ^ d ∂ξ) - B.qVal h|) ^ 2
      ≤ (1 + 2 * Mc * K₁ ^ 2) * (Δ ^ 2 + T ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hsq hMc0
    have h2 : Mc * (2 * K₁ ^ 2 * T ^ 2 + 2 * Δ ^ 2)
        ≤ (1 + 2 * Mc * K₁ ^ 2) * (Δ ^ 2 + T ^ 2) := by
      have hK2 : 1 ≤ K₁ ^ 2 := by nlinarith
      nlinarith [sq_nonneg T, sq_nonneg Δ, mul_nonneg hMc0 (sq_nonneg Δ)]
    linarith
  have hAcoef : -((d : ℝ) ^ 3 / 24 / 2) * A ≤ -((d : ℝ) ^ 3 / 192 + (d : ℝ) ^ 3 / 192) * A := by
    nlinarith
  linarith

/-- **`lem:first-variation-bound` and `lem:central-kernel-bound` with the same `a`.**  The paper's
`lem:central-kernel-bound` refers to "the constant `a` from `lem:first-variation-bound`"; here
both lemmas are stated with one `a > 0`. -/
theorem first_variation_central_kernel_bounds (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ a : ℝ, 0 < a ∧
      (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∃ b hρ : ℝ, 0 < b ∧ 0 < hρ ∧ hρ ≤ B.h₀ ∧ ∀ h : ℝ, 0 < h → h < hρ →
          (∀ x ∈ openWindow d ρ, a * B.Qh h x ^ 2 ≤ B.PsiT h x) ∧
          (∀ x ∈ Set.Icc (0 : ℝ) 2 \ openWindow d ρ, b ≤ B.PsiT h x)) ∧
      (∃ ρ₀ C : ℝ, 0 < ρ₀ ∧ 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧ ∀ h : ℝ, 0 < h → h < hρ →
          ∀ ξ : Measure ℝ, IsProbabilityMeasure ξ → ξ (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
            -(a / 2) * (∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂ξ)
              - C * (((∫ x, x ^ d ∂ξ) - B.qVal h) ^ 2
                  + (ξ (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal ^ 2)
            ≤ B.sigmaInt h ξ (openWindow d ρ)
                (fun x => B.sigmaInt h ξ (openWindow d ρ) (fun y => B.contKernel h x y))) := by
  have hdR : (0 : ℝ) < (d : ℝ) := dpos hd
  exact ⟨(d : ℝ) ^ 3 / 24, by positivity, first_variation_bound hd B, central_kernel_bound hd B⟩

end SingularEndpoint

end UpperTailOptimizers
