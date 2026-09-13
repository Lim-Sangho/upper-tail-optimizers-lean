import UpperTailOptimizers.SingularEndpoint.FirstVariationCentralKernel
import UpperTailOptimizers.SingularEndpoint.NonlinearLagrangian
import UpperTailOptimizers.SingularEndpoint.GraphonComparisonMaster

/-!
# `lem:auxiliary-lagrangian-bound` in the form of the paper

`lem:auxiliary-lagrangian-bound` (`paper/sections/singular_auxiliary_lagrangian.tex`): there
are `ρ₀ > 0`, `a > 0` and `C_{d,m} ≥ 1` such that for every `0 < ρ < ρ₀` there are
`b_ρ, h_ρ > 0` with, for `0 < h < h_ρ`, `W` as in `lem:localization-rank-one` with its
decomposition `W = f ⊗ f + E`, and `ν` the law of `f`,

`𝓛_h(ν) - 𝓛_h(ν_h) ≥ (a/2) A_{h,ρ}(ν) + (b_ρ/2) ν(𝒯_ρ) - C_{d,m} Δ_h(ν)²`,

with the open window `𝒩_ρ`, the closed tail `𝒯_ρ = [0,2] ∖ 𝒩_ρ`, and the nonlinear auxiliary
Lagrangian `𝓛_h(ξ) = 𝒥_h(ξ) - μ_h{m_d(ξ)^v - q_h^v}` (`KKTFamily.auxLagrangian`).

The proof follows the paper's:

* `distributionJ_sub_eq`: `𝒥_h(ν) - 𝒥_h(ν_h) - η_hΔ = ∫Ψ_h dν + ∬K_h dσdσ`;
* `first_variation_bound`: `∫Ψ_h dν ≥ a A_{h,ρ} + b_ρ ν(𝒯_ρ)`;
* `sigmaQuad_split_set`: the split of `∬K_h dσdσ` over `𝒩_ρ ⊔ 𝒯_ρ`;
* `central_kernel_bound` for `𝒩_ρ²`, with a constant independent of `ρ`;
* `abs_sigmaInt_le_of_holder`, fed with the `1/2`-Hölder bound and the sup bound of
  `continuation_kernel_bounds`, for the two mixed terms and the tail term:
  their sum is at most `2C ν(𝒯_ρ)(∫|x - u_h|^{1/2}dν + h^{1/2}) + 3C ν(𝒯_ρ)²`;
* `auxLagrangian_gap_ge`: the nonlinear correction costs `|μ_h| v²(2^d)^{2v} Δ²`.

`auxiliary_gap_bound_law` (linear moment correction) and `auxiliary_lagrangian_bound_law`
(nonlinear correction) are the measure-level forms, with the two a-priori quantities
`∫|x - u_h|^{1/2}dν ≤ K h^{1/2}` and `ν(𝒯_ρ) ≤ K h⁴` as hypotheses.  The lemma itself, for the
decomposition of `lem:localization-rank-one` and `ν` the law of `f`, is
`auxiliary_lagrangian_bound` in `SingularEndpoint/GraphonLagrangianBound.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## Elementary facts about the open window -/

theorem openWindow_subset_Icc (hd : 2 ≤ d) {ρ : ℝ} (hρu : ρ ≤ uStar d / 2)
    (hρ1 : ρ ≤ (1 - uStar d) / 2) : openWindow d ρ ⊆ Set.Icc (0 : ℝ) 2 := by
  have hu0 := uStar_pos hd
  have hu1 := uStar_lt_one hd
  intro x hx
  have h1 : uStar d - ρ < x := hx.1
  have h2 : x < uStar d + ρ := hx.2
  exact ⟨by linarith, by linarith⟩

theorem measureReal_add_tail {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {S : Set ℝ} (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Icc (0 : ℝ) 2) :
    (ν S).toReal + (ν (Set.Icc (0 : ℝ) 2 \ S)).toReal = 1 := by
  have hsplit : ν (Set.Icc (0 : ℝ) 2 ∩ S) + ν (Set.Icc (0 : ℝ) 2 \ S) = ν (Set.Icc (0 : ℝ) 2) :=
    measure_inter_add_sdiff _ hS
  rw [Set.inter_eq_right.mpr hSsub, (prob_compl_eq_zero_iff measurableSet_Icc).mp hν] at hsplit
  rw [← ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _), hsplit, ENNReal.toReal_one]

namespace KKTFamily

/-! ## Splitting the `σ`-integrals over `S ⊔ ([0,2] ∖ S)` -/

theorem sVal_mem_Icc {B : KKTFamily d} {h : ℝ} (hh : |h| < B.h₀) :
    B.sVal h ∈ Set.Icc (0 : ℝ) 2 := ⟨(sVal_pos hh).le, by linarith [sVal_lt_one hh]⟩

theorem tVal_mem_Icc {B : KKTFamily d} {h : ℝ} (hh : |h| < B.h₀) :
    B.tVal h ∈ Set.Icc (0 : ℝ) 2 := ⟨(tVal_pos hh).le, by linarith [tVal_lt_one hh]⟩

theorem u_mem_Icc {B : KKTFamily d} {h : ℝ} (hh : |h| < B.h₀) : B.u h ∈ Set.Icc (0 : ℝ) 2 := by
  obtain ⟨h1, h2⟩ := B.factor_mem h hh
  have := abs_nonneg h
  exact ⟨by linarith, by linarith⟩

/-- `∫_{[0,2]} f dσ = ∫_S f dσ + ∫_{[0,2]∖S} f dν` when both atoms lie in `S`. -/
theorem sigmaInt_Icc_split (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {S : Set ℝ} (hS : MeasurableSet S)
    (hs : B.sVal h ∈ S) (ht : B.tVal h ∈ S) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 2)) :
    B.sigmaInt h ν (Set.Icc (0 : ℝ) 2) f
      = B.sigmaInt h ν S f + ∫ x in Set.Icc (0 : ℝ) 2 \ S, f x ∂ν := by
  have := isProbabilityMeasure_distributionMeasure B hh
  have hz : B.distributionMeasure h (Set.Icc (0 : ℝ) 2 \ S) = 0 :=
    distributionMeasure_eq_zero_of_notMem B h (fun hx => hx.2 hs) (fun hx => hx.2 ht)
  rw [sigmaInt, sigmaInt, integral_Icc_split hν hf hS,
    integral_Icc_split (distributionMeasure_Icc_compl B hh) hf hS,
    Measure.restrict_eq_zero.mpr hz, integral_zero_measure]
  ring

theorem restrict_support {ν : Measure ℝ} (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (S : Set ℝ) :
    (ν.restrict S) (Set.Icc (0 : ℝ) 2)ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Icc.compl]
  exact measure_mono_null Set.inter_subset_left hν

/-- The inner window integral `x ↦ ∫_S K_h(x,y) dσ(y)` is continuous on `[0,2]`. -/
theorem continuousOn_sigmaInt_contKernel (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    {S : Set ℝ} (hs : B.sVal h ∈ S) (ht : B.tVal h ∈ S) :
    ContinuousOn (fun x => B.sigmaInt h ν S (fun y => B.contKernel h x y)) (Set.Icc 0 2) := by
  have h1 : ContinuousOn (fun x => ∫ y, B.JpTildeH h (x * y) ∂(ν.restrict S)) (Set.Icc 0 2) :=
    continuousOn_innerIntegral (restrict_support hν S) (continuousOn_JpTildeH hd B h)
  have h2 := continuousOn_crossK hd B hh
  refine (h1.sub h2).congr fun x _ => ?_
  simp only [sigmaInt, contKernel, Pi.sub_apply]
  rw [distributionMeasure_restrict_of_mem B hs ht, integral_distributionMeasure_kernel B hh]

/-- The tail integral `x ↦ ∫_T K_h(x,y) dν(y)` is continuous on `[0,2]`. -/
theorem continuousOn_setIntegral_contKernel (hd : 2 ≤ d) (B : KKTFamily d) (h : ℝ)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) (T : Set ℝ) :
    ContinuousOn (fun x => ∫ y in T, B.contKernel h x y ∂ν) (Set.Icc 0 2) :=
  continuousOn_innerIntegral (restrict_support hν T) (continuousOn_JpTildeH hd B h)

/-- **The split of `∬K_h dσdσ` over `S ⊔ T`, `T = [0,2] ∖ S`**, for a measurable `S ⊆ [0,2]`
containing both atoms:

`∬K_h dσdσ = ∫_S∫_S K_h dσdσ + ∫_S(∫_T K_h dν)dσ + ∫_T(∫_S K_h dσ)dν + ∫_T∫_T K_h dνdν`. -/
theorem sigmaQuad_split_set (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {S : Set ℝ}
    (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc (0 : ℝ) 2) (hs : B.sVal h ∈ S)
    (ht : B.tVal h ∈ S) :
    B.sigmaQuad h ν
      = B.sigmaInt h ν S (fun x => B.sigmaInt h ν S (fun y => B.contKernel h x y))
        + B.sigmaInt h ν S (fun x => ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν)
        + ∫ x in Set.Icc (0 : ℝ) 2 \ S, B.sigmaInt h ν S (fun y => B.contKernel h x y) ∂ν
        + ∫ x in Set.Icc (0 : ℝ) 2 \ S, (∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν) ∂ν := by
  have hT : MeasurableSet (Set.Icc (0 : ℝ) 2 \ S) := measurableSet_Icc.diff hS
  have hcS := continuousOn_sigmaInt_contKernel hd B hh hν hs ht
  have hcT := continuousOn_setIntegral_contKernel hd B h hν (Set.Icc (0 : ℝ) 2 \ S)
  -- the inner split
  have hinner : ∀ x ∈ Set.Icc (0 : ℝ) 2,
      B.sigmaInt h ν (Set.Icc 0 2) (fun y => B.JpTildeH h (x * y))
        = B.sigmaInt h ν S (fun y => B.contKernel h x y)
          + ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν := fun x hx =>
    sigmaInt_Icc_split B hh hν hS hs ht (continuousOn_distributionIntegrand hd B h hx.1 hx.2)
  have hcG : ContinuousOn (fun x => B.sigmaInt h ν (Set.Icc 0 2) (fun y => B.JpTildeH h (x * y)))
      (Set.Icc 0 2) := (hcS.add hcT).congr fun x hx => hinner x hx
  -- the outer split
  have hiS : IntegrableOn (fun x => B.sigmaInt h ν S (fun y => B.contKernel h x y)) S ν :=
    (integrableOn_of_continuousOn hν hcS isCompact_Icc).mono_set hSsub
  have hiT : IntegrableOn (fun x => ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν) S ν :=
    (integrableOn_of_continuousOn hν hcT isCompact_Icc).mono_set hSsub
  have hiS' : IntegrableOn (fun x => B.sigmaInt h ν S (fun y => B.contKernel h x y))
      (Set.Icc (0 : ℝ) 2 \ S) ν :=
    (integrableOn_of_continuousOn hν hcS isCompact_Icc).mono_set Set.sdiff_subset
  have hiT' : IntegrableOn (fun x => ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν)
      (Set.Icc (0 : ℝ) 2 \ S) ν :=
    (integrableOn_of_continuousOn hν hcT isCompact_Icc).mono_set Set.sdiff_subset
  rw [sigmaQuad_eq_sigmaInt hd B hh hν, sigmaInt_Icc_split B hh hν hS hs ht hcG]
  have hS1 : B.sigmaInt h ν S (fun x => B.sigmaInt h ν (Set.Icc 0 2) (fun y => B.JpTildeH h (x * y)))
      = B.sigmaInt h ν S (fun x => B.sigmaInt h ν S (fun y => B.contKernel h x y))
        + B.sigmaInt h ν S (fun x => ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν) := by
    have e1 := sigmaInt_of_atoms_mem B hh ν hs ht
      (fun x => B.sigmaInt h ν (Set.Icc 0 2) (fun y => B.JpTildeH h (x * y)))
    have e2 := sigmaInt_of_atoms_mem B hh ν hs ht
      (fun x => B.sigmaInt h ν S (fun y => B.contKernel h x y))
    have e3 := sigmaInt_of_atoms_mem B hh ν hs ht
      (fun x => ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν)
    have hcongr : ∫ x in S, B.sigmaInt h ν (Set.Icc 0 2) (fun y => B.JpTildeH h (x * y)) ∂ν
        = ∫ x in S, (B.sigmaInt h ν S (fun y => B.contKernel h x y)
            + ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν) ∂ν :=
      setIntegral_congr_fun hS (fun x hx => hinner x (hSsub hx))
    have hsv := hinner _ (hSsub hs)
    have htv := hinner _ (hSsub ht)
    rw [e1, e2, e3, hcongr, integral_add hiS hiT, hsv, htv]
    ring
  have hT1 : ∫ x in Set.Icc (0 : ℝ) 2 \ S,
        B.sigmaInt h ν (Set.Icc 0 2) (fun y => B.JpTildeH h (x * y)) ∂ν
      = (∫ x in Set.Icc (0 : ℝ) 2 \ S, B.sigmaInt h ν S (fun y => B.contKernel h x y) ∂ν)
        + ∫ x in Set.Icc (0 : ℝ) 2 \ S,
            (∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν) ∂ν := by
    rw [setIntegral_congr_fun hT (fun x hx => hinner x hx.1), integral_add hiS' hiT']
  rw [hS1, hT1]
  ring

/-! ## The Hölder bound for a `σ`-integral over `S` -/

/-- **A `σ`-integral over `S` of a function `1/2`-Hölder at `u_h`.**  If `|g(x) - g(u_h)| ≤
L|x - u_h|^{1/2}` on `[0,2]` and `|g(u_h)| ≤ M`, then

`|∫_S g dσ| ≤ L ∫|x - u_h|^{1/2}dν + L h^{1/2} + M ν([0,2] ∖ S)`.

The atoms of `ν_h` sit at `u_h ∓ h`, and `σ(S) = -ν([0,2] ∖ S)`. -/
theorem abs_sigmaInt_le_of_holder (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (hh0 : 0 ≤ h) {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc (0 : ℝ) 2) (hs : B.sVal h ∈ S)
    (ht : B.tVal h ∈ S) {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 2)) {L M : ℝ} (hL : 0 ≤ L)
    (hgH : ∀ x ∈ Set.Icc (0 : ℝ) 2, |g x - g (B.u h)| ≤ L * Real.sqrt |x - B.u h|)
    (hgM : |g (B.u h)| ≤ M) :
    |B.sigmaInt h ν S g|
      ≤ L * (∫ x, Real.sqrt |x - B.u h| ∂ν) + L * Real.sqrt h
        + M * (ν (Set.Icc (0 : ℝ) 2 \ S)).toReal := by
  have hu := u_mem_Icc hh
  have ha := B.alph_mem h hh
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hgM
  rw [sigmaInt_of_atoms_mem B hh ν hs ht]
  have hig : IntegrableOn g S ν := (integrableOn_of_continuousOn hν hg isCompact_Icc).mono_set hSsub
  have hisq : Integrable (fun x => Real.sqrt |x - B.u h|) ν :=
    integrable_of_continuousOn hν (by fun_prop)
  have hsplit : ∫ x in S, g x ∂ν
      = (∫ x in S, (g x - g (B.u h)) ∂ν) + g (B.u h) * (ν S).toReal := by
    rw [integral_sub hig (integrableOn_const (measure_ne_top _ _)), setIntegral_const,
      smul_eq_mul, measureReal_def]
    ring
  have hb1 : |∫ x in S, (g x - g (B.u h)) ∂ν| ≤ L * ∫ x, Real.sqrt |x - B.u h| ∂ν := by
    have h1 : |∫ x in S, (g x - g (B.u h)) ∂ν| ≤ ∫ x in S, |g x - g (B.u h)| ∂ν := by
      have := norm_integral_le_integral_norm (μ := ν.restrict S) (fun x => g x - g (B.u h))
      simpa [Real.norm_eq_abs] using this
    have h2 : ∫ x in S, |g x - g (B.u h)| ∂ν ≤ ∫ x in S, L * Real.sqrt |x - B.u h| ∂ν :=
      setIntegral_mono_on (hig.sub (integrableOn_const (measure_ne_top _ _))).abs
        (hisq.const_mul L).integrableOn hS (fun x hx => hgH x (hSsub hx))
    have h3 : ∫ x in S, L * Real.sqrt |x - B.u h| ∂ν ≤ ∫ x, L * Real.sqrt |x - B.u h| ∂ν :=
      setIntegral_le_integral (hisq.const_mul L)
        (Filter.Eventually.of_forall fun x => mul_nonneg hL (Real.sqrt_nonneg _))
    have h4 : ∫ x, L * Real.sqrt |x - B.u h| ∂ν = L * ∫ x, Real.sqrt |x - B.u h| ∂ν :=
      integral_const_mul L _
    linarith
  have hsu : |B.sVal h - B.u h| = h := by
    rw [sVal, show B.u h - h - B.u h = -h by ring, abs_neg, abs_of_nonneg hh0]
  have htu : |B.tVal h - B.u h| = h := by
    rw [tVal, show B.u h + h - B.u h = h by ring, abs_of_nonneg hh0]
  have hb2 : |g (B.sVal h) - g (B.u h)| ≤ L * Real.sqrt h := by
    have := hgH _ (sVal_mem_Icc hh); rwa [hsu] at this
  have hb3 : |g (B.tVal h) - g (B.u h)| ≤ L * Real.sqrt h := by
    have := hgH _ (tVal_mem_Icc hh); rwa [htu] at this
  have hSt : (ν S).toReal = 1 - (ν (Set.Icc (0 : ℝ) 2 \ S)).toReal := by
    linarith [measureReal_add_tail hν hS hSsub]
  set t := (ν (Set.Icc (0 : ℝ) 2 \ S)).toReal with ht_def
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have heq : (∫ x in S, g x ∂ν) - (B.alph h * g (B.sVal h) + (1 - B.alph h) * g (B.tVal h))
      = (∫ x in S, (g x - g (B.u h)) ∂ν) - B.alph h * (g (B.sVal h) - g (B.u h))
        - (1 - B.alph h) * (g (B.tVal h) - g (B.u h)) - g (B.u h) * t := by
    rw [hsplit, hSt]; ring
  rw [heq]
  have e1 := abs_sub (∫ x in S, (g x - g (B.u h)) ∂ν - B.alph h * (g (B.sVal h) - g (B.u h))
      - (1 - B.alph h) * (g (B.tVal h) - g (B.u h))) (g (B.u h) * t)
  have e2 := abs_sub (∫ x in S, (g x - g (B.u h)) ∂ν - B.alph h * (g (B.sVal h) - g (B.u h)))
    ((1 - B.alph h) * (g (B.tVal h) - g (B.u h)))
  have e3 := abs_sub (∫ x in S, (g x - g (B.u h)) ∂ν) (B.alph h * (g (B.sVal h) - g (B.u h)))
  have e4 : |B.alph h * (g (B.sVal h) - g (B.u h))| ≤ B.alph h * (L * Real.sqrt h) := by
    rw [abs_mul, abs_of_pos ha.1]; exact mul_le_mul_of_nonneg_left hb2 ha.1.le
  have e5 : |(1 - B.alph h) * (g (B.tVal h) - g (B.u h))| ≤ (1 - B.alph h) * (L * Real.sqrt h) := by
    rw [abs_mul, abs_of_pos (by linarith [ha.2] : (0 : ℝ) < 1 - B.alph h)]
    exact mul_le_mul_of_nonneg_left hb3 (by linarith [ha.2])
  have e6 : |g (B.u h) * t| ≤ M * t := by
    rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_mul_of_nonneg_right hgM ht0
  have e7 : B.alph h * (L * Real.sqrt h) + (1 - B.alph h) * (L * Real.sqrt h) = L * Real.sqrt h := by
    ring
  linarith

/-! ## The first-variation term -/

/-- `∫Ψ_h dν ≥ a ∫_S Q_h² dν + b ν([0,2] ∖ S)` from the pointwise bounds on `S` and on the tail. -/
theorem integral_PsiT_ge (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 2)ᶜ = 0) {S : Set ℝ}
    (hS : MeasurableSet S) {a b : ℝ}
    (ha : ∀ x ∈ S, a * B.Qh h x ^ 2 ≤ B.PsiT h x)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 2 \ S, b ≤ B.PsiT h x) :
    a * (∫ x in S, B.Qh h x ^ 2 ∂ν) + b * (ν (Set.Icc (0 : ℝ) 2 \ S)).toReal
      ≤ ∫ x, B.PsiT h x ∂ν := by
  have hcP := continuousOn_PsiT hd B hh
  have hcQ : ContinuousOn (fun x => a * B.Qh h x ^ 2) (Set.Icc 0 2) := by
    simp only [Qh]; fun_prop
  have hT : MeasurableSet (Set.Icc (0 : ℝ) 2 \ S) := measurableSet_Icc.diff hS
  have hiP : Integrable (B.PsiT h) ν := integrable_of_continuousOn hν hcP
  have hiQ : Integrable (fun x => a * B.Qh h x ^ 2) ν := integrable_of_continuousOn hν hcQ
  have h1 : ∫ x in S, a * B.Qh h x ^ 2 ∂ν ≤ ∫ x in S, B.PsiT h x ∂ν :=
    setIntegral_mono_on hiQ.integrableOn hiP.integrableOn hS ha
  have h2 : ∫ x in Set.Icc (0 : ℝ) 2 \ S, b ∂ν ≤ ∫ x in Set.Icc (0 : ℝ) 2 \ S, B.PsiT h x ∂ν :=
    setIntegral_mono_on (integrableOn_const (measure_ne_top _ _)) hiP.integrableOn hT hb
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h2
  rw [integral_const_mul] at h1
  have hsplit : ∫ x, B.PsiT h x ∂ν
      = (∫ x in S, B.PsiT h x ∂ν) + ∫ x in Set.Icc (0 : ℝ) 2 \ S, B.PsiT h x ∂ν := by
    have h3 : ∫ x in S, B.PsiT h x ∂ν + ∫ x in Sᶜ, B.PsiT h x ∂ν = ∫ x, B.PsiT h x ∂ν :=
      integral_add_compl hS hiP
    have h4 : ∫ x in Sᶜ, B.PsiT h x ∂ν = ∫ x in Set.Icc (0 : ℝ) 2 \ S, B.PsiT h x ∂ν := by
      rw [← restrict_Icc_inter hν Sᶜ, Set.sdiff_eq]
    linarith
  rw [hsplit]
  linarith

end KKTFamily

/-! ## The measure-level lemma -/

set_option maxHeartbeats 4000000 in
/-- **`lem:auxiliary-lagrangian-bound`, measure-level form with the linear moment correction.**
There are `ρ₀ > 0` and `C ≥ 1` such that for every `0 < ρ < ρ₀` there is `b > 0`, and for every
`K ≥ 0` there is `0 < h_ρ ≤ h₀`, with, for all `0 < h < h_ρ` and every probability measure `ν`
on `[0,2]` satisfying `∫|x - u_h|^{1/2}dν ≤ Kh^{1/2}` and `ν(𝒯_ρ) ≤ Kh⁴`,

`(a/2) A_{h,ρ}(ν) + (b/2) ν(𝒯_ρ) - C Δ_h(ν)² ≤ 𝒥_h(ν) - 𝒥_h(ν_h) - η_hΔ_h(ν)`,   `a = d³/24`.

No graph enters: `C` is the constant of `central_kernel_bound`, and it depends neither on `ρ` nor
on `K`; `b` does not depend on `K`.  The nonlinear form is `auxiliary_lagrangian_bound_law`. -/
theorem auxiliary_gap_bound_law (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ₀ C : ℝ, 0 < ρ₀ ∧ 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      ∃ b : ℝ, 0 < b ∧ ∀ K : ℝ, 0 ≤ K → ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧
        ∀ h : ℝ, 0 < h → h < hρ →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          (∫ x, Real.sqrt |x - B.u h| ∂ν) ≤ K * Real.sqrt h →
          (ν (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal ≤ K * h ^ 4 →
          (d : ℝ) ^ 3 / 24 / 2 * (∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂ν)
              + b / 2 * (ν (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
              - C * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2
            ≤ B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
                - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h) := by
  classical
  obtain ⟨ρC, CC, hρC, hCC1, hcentral⟩ := central_kernel_bound hd B
  obtain ⟨ρF, hρF, hfirst⟩ := first_variation_bound hd B
  obtain ⟨CL, hL₀, hCL1, hL₀pos, hL₀le, hLbd⟩ := continuation_kernel_bounds hd B
  have hu0 := uStar_pos hd
  have hu1 := uStar_lt_one hd
  refine ⟨min (min ρC ρF) (min (uStar d / 2) ((1 - uStar d) / 2)), CC,
    lt_min (lt_min hρC hρF) (lt_min (by linarith) (by linarith)), hCC1, ?_⟩
  intro ρ hρ0 hρlt
  have hρC' : ρ < ρC := lt_of_lt_of_le hρlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρF' : ρ < ρF := lt_of_lt_of_le hρlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρu : ρ ≤ uStar d / 2 :=
    le_trans hρlt.le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ1 : ρ ≤ (1 - uStar d) / 2 :=
    le_trans hρlt.le (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨b, hF, hb0, hF0, hFle, hPsi⟩ := hfirst ρ hρ0 hρF'
  obtain ⟨hC, hC0, hCle, hcent⟩ := hcentral ρ hρ0 hρC'
  refine ⟨b, hb0, fun K hK => ?_⟩
  obtain ⟨δa, hδa, hatoms⟩ := B.exists_atoms_mem_centralWindow (half_pos hρ0)
  -- smallness of the error bracket `2CL(K+1)√h + (CC + 3CL)Kh⁴ ≤ b/2`
  have hsmall : ∃ δs : ℝ, 0 < δs ∧ ∀ h : ℝ, 0 < h → h < δs →
      2 * CL * (K + 1) * Real.sqrt h + (CC + 3 * CL) * (K * h ^ 4) ≤ b / 2 := by
    obtain ⟨ε, hε, hεdef⟩ : ∃ ε : ℝ, 0 < ε ∧ ε = b / (4 * (2 * CL * (K + 1) + (CC + 3 * CL) * K + 1)) :=
      ⟨_, by positivity, rfl⟩
    refine ⟨min (ε ^ 2) 1, lt_min (by positivity) one_pos, fun h hh0 hhlt => ?_⟩
    have hh1 : h ≤ 1 := le_trans hhlt.le (min_le_right _ _)
    have hsq : Real.sqrt h ≤ ε := by
      rw [show ε = Real.sqrt (ε ^ 2) by rw [Real.sqrt_sq hε.le]]
      exact Real.sqrt_le_sqrt (le_trans hhlt.le (min_le_left _ _))
    have hh4 : h ^ 4 ≤ Real.sqrt h := by
      have h2 : h ≤ Real.sqrt h := by
        have hs1 : Real.sqrt h ≤ 1 := by
          calc Real.sqrt h ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hh1
            _ = 1 := Real.sqrt_one
        calc h = Real.sqrt h * Real.sqrt h := (Real.mul_self_sqrt hh0.le).symm
          _ ≤ Real.sqrt h * 1 := mul_le_mul_of_nonneg_left hs1 (Real.sqrt_nonneg h)
          _ = Real.sqrt h := mul_one _
      have h3 : h ^ 4 ≤ h := by
        calc h ^ 4 = h * h ^ 3 := by ring
          _ ≤ h * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hh0.le hh1) hh0.le
          _ = h := mul_one h
      linarith
    have hden : 0 < 2 * CL * (K + 1) + (CC + 3 * CL) * K + 1 := by positivity
    have hkey : (2 * CL * (K + 1) + (CC + 3 * CL) * K) * Real.sqrt h ≤ b / 4 := by
      have h1 : (2 * CL * (K + 1) + (CC + 3 * CL) * K) * Real.sqrt h
          ≤ (2 * CL * (K + 1) + (CC + 3 * CL) * K + 1) * ε :=
        mul_le_mul (by linarith) hsq (Real.sqrt_nonneg _) hden.le
      have h2 : (2 * CL * (K + 1) + (CC + 3 * CL) * K + 1) * ε = b / 4 := by
        rw [hεdef]; field_simp
      linarith
    have hK4 : (CC + 3 * CL) * (K * h ^ 4) ≤ (CC + 3 * CL) * K * Real.sqrt h := by
      have := mul_le_mul_of_nonneg_left hh4 (by positivity : (0 : ℝ) ≤ (CC + 3 * CL) * K)
      linarith
    nlinarith
  obtain ⟨δs, hδs, hsm⟩ := hsmall
  refine ⟨min (min (min hF hC) hL₀) (min (min δa δs) B.h₀),
    lt_min (lt_min (lt_min hF0 hC0) hL₀pos) (lt_min (lt_min hδa hδs) B.h₀_pos),
    le_trans (min_le_right _ _) (min_le_right _ _), ?_⟩
  intro h hpos hlt ν hνprob hν hI htail
  have hhF : h < hF := lt_of_lt_of_le hlt (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hhC : h < hC := lt_of_lt_of_le hlt (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hhL : h < hL₀ := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hha : h < δa := lt_of_lt_of_le hlt (le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hhs : h < δs := lt_of_lt_of_le hlt (le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hhB : |h| < B.h₀ := by
    rw [abs_of_pos hpos]
    exact lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the sets
  set S := openWindow d ρ with hSdef
  have hS : MeasurableSet S := measurableSet_openWindow d ρ
  have hSsub : S ⊆ Set.Icc (0 : ℝ) 2 := openWindow_subset_Icc hd hρu hρ1
  obtain ⟨hs2, ht2⟩ := hatoms h hpos hha
  have hsS : B.sVal h ∈ S := by
    have h1 : B.sVal h ∈ Set.Icc (uStar d - ρ / 2) (uStar d + ρ / 2) := hs2
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have htS : B.tVal h ∈ S := by
    have h1 : B.tVal h ∈ Set.Icc (uStar d - ρ / 2) (uStar d + ρ / 2) := ht2
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  -- the continuation bounds at this `h`
  obtain ⟨-, -, -, hKH, -, hKbd⟩ := hLbd h hpos.le hhL
  have hKsymm : ∀ x y : ℝ, B.contKernel h x y = B.contKernel h y x := fun x y => by
    simp only [KKTFamily.contKernel, mul_comm]
  have hu := KKTFamily.u_mem_Icc hhB
  set t := (ν (Set.Icc (0 : ℝ) 2 \ S)).toReal with htdef
  set I := ∫ x, Real.sqrt |x - B.u h| ∂ν with hIdef
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hI0 : 0 ≤ I := integral_nonneg fun x => Real.sqrt_nonneg _
  -- the four pieces of `∬K dσdσ`
  have hsplitQ := KKTFamily.sigmaQuad_split_set hd B hhB hν hS hSsub hsS htS
  have hcentralB := hcent h hpos hhC ν hνprob hν
  -- mixed term 1: `∫_S (∫_T K dν) dσ`
  have hFT : ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ x' ∈ Set.Icc (0 : ℝ) 2,
      |(∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν)
          - ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x' y ∂ν|
        ≤ CL * Real.sqrt |x - x'| * t := by
    intro x hx x' hx'
    have hint : ∀ z ∈ Set.Icc (0 : ℝ) 2,
        IntegrableOn (fun y => B.contKernel h z y) (Set.Icc (0 : ℝ) 2 \ S) ν := fun z hz =>
      (integrableOn_of_continuousOn hν (KKTFamily.continuousOn_distributionIntegrand hd B h hz.1 hz.2)
        isCompact_Icc).mono_set Set.sdiff_subset
    rw [← integral_sub (hint x hx) (hint x' hx')]
    have hb : ∀ y ∈ Set.Icc (0 : ℝ) 2 \ S,
        ‖B.contKernel h x y - B.contKernel h x' y‖ ≤ CL * Real.sqrt |x - x'| := fun y hy => by
      rw [Real.norm_eq_abs]; exact hKH x hx x' hx' y hy.1
    have := norm_setIntegral_le_of_norm_le_const (μ := ν) (measure_lt_top ν _) hb
    simpa [Real.norm_eq_abs, measureReal_def] using this
  have hFTbd : ∀ x ∈ Set.Icc (0 : ℝ) 2,
      |∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν| ≤ CL * t := by
    intro x hx
    have hb : ∀ y ∈ Set.Icc (0 : ℝ) 2 \ S, ‖B.contKernel h x y‖ ≤ CL := fun y hy => by
      rw [Real.norm_eq_abs]; exact hKbd x hx y hy.1
    have := norm_setIntegral_le_of_norm_le_const (μ := ν) (measure_lt_top ν _) hb
    simpa [Real.norm_eq_abs, measureReal_def] using this
  have hM1 := KKTFamily.abs_sigmaInt_le_of_holder B hhB hpos.le hν hS hSsub hsS htS
    (g := fun x => ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν)
    (KKTFamily.continuousOn_setIntegral_contKernel hd B h hν _)
    (L := CL * t) (M := CL * t) (by positivity)
    (fun x hx => by
      have := hFT x hx (B.u h) hu
      linarith [show CL * Real.sqrt |x - B.u h| * t = CL * t * Real.sqrt |x - B.u h| by ring])
    (hFTbd (B.u h) hu)
  -- the pointwise bound on the inner window integral
  have hFS : ∀ x ∈ Set.Icc (0 : ℝ) 2,
      |B.sigmaInt h ν S (fun y => B.contKernel h x y)| ≤ CL * I + CL * Real.sqrt h + CL * t := by
    intro x hx
    exact KKTFamily.abs_sigmaInt_le_of_holder B hhB hpos.le hν hS hSsub hsS htS
      (g := fun y => B.contKernel h x y)
      (KKTFamily.continuousOn_distributionIntegrand hd B h hx.1 hx.2) (L := CL) (M := CL) (by linarith)
      (fun y hy => by
        rw [hKsymm x y, hKsymm x (B.u h)]
        exact hKH y hy (B.u h) hu x hx)
      (hKbd x hx (B.u h) hu)
  -- mixed term 2: `∫_T (∫_S K dσ) dν`
  have hM2 : |∫ x in Set.Icc (0 : ℝ) 2 \ S, B.sigmaInt h ν S (fun y => B.contKernel h x y) ∂ν|
      ≤ (CL * I + CL * Real.sqrt h + CL * t) * t := by
    have hb : ∀ x ∈ Set.Icc (0 : ℝ) 2 \ S,
        ‖B.sigmaInt h ν S (fun y => B.contKernel h x y)‖ ≤ CL * I + CL * Real.sqrt h + CL * t :=
      fun x hx => by rw [Real.norm_eq_abs]; exact hFS x hx.1
    have := norm_setIntegral_le_of_norm_le_const (μ := ν) (measure_lt_top ν _) hb
    simpa [Real.norm_eq_abs, measureReal_def] using this
  -- the tail term `∫_T∫_T K dν dν`
  have hTT : |∫ x in Set.Icc (0 : ℝ) 2 \ S, (∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν) ∂ν|
      ≤ CL * t * t := by
    have hb : ∀ x ∈ Set.Icc (0 : ℝ) 2 \ S,
        ‖∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν‖ ≤ CL * t :=
      fun x hx => by rw [Real.norm_eq_abs]; exact hFTbd x hx.1
    have := norm_setIntegral_le_of_norm_le_const (μ := ν) (measure_lt_top ν _) hb
    simpa [Real.norm_eq_abs, measureReal_def] using this
  -- the first-variation term
  obtain ⟨hPsiS, hPsiT⟩ := hPsi h hpos hhF
  have hΨ := KKTFamily.integral_PsiT_ge hd B hhB hν hS hPsiS hPsiT
  -- the exact expansion and the nonlinear correction
  have hexp := KKTFamily.distributionJ_sub_eq hd B hhB ν hν
  -- assemble
  set A := ∫ x in S, B.Qh h x ^ 2 ∂ν with hAdef
  set Δ := (∫ x, x ^ d ∂ν) - B.qVal h with hΔdef
  have hA0 : 0 ≤ A := setIntegral_nonneg hS fun x _ => sq_nonneg _
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have hsm' := hsm h hpos hhs
  have hIK : I ≤ K * Real.sqrt h := hI
  have htK : t ≤ K * h ^ 4 := htail
  have hsqrt0 : 0 ≤ Real.sqrt h := Real.sqrt_nonneg h
  -- the error bracket is at most `b/2`
  have hbracket : CC * t + 2 * (CL * I + CL * Real.sqrt h) + 3 * CL * t ≤ b / 2 := by
    have h1 : CL * I ≤ CL * (K * Real.sqrt h) := mul_le_mul_of_nonneg_left hIK (by linarith)
    have h2 : CC * t ≤ CC * (K * h ^ 4) := mul_le_mul_of_nonneg_left htK (by linarith)
    have h3 : 3 * CL * t ≤ 3 * CL * (K * h ^ 4) := mul_le_mul_of_nonneg_left htK (by linarith)
    nlinarith
  have hloss : |B.sigmaInt h ν S (fun x => ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν)|
      + |∫ x in Set.Icc (0 : ℝ) 2 \ S, B.sigmaInt h ν S (fun y => B.contKernel h x y) ∂ν|
      + |∫ x in Set.Icc (0 : ℝ) 2 \ S, (∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν) ∂ν|
      ≤ t * (2 * (CL * I + CL * Real.sqrt h) + 3 * CL * t) := by
    nlinarith [hM1, hM2, hTT]
  have hlossb : t * (CC * t + 2 * (CL * I + CL * Real.sqrt h) + 3 * CL * t) ≤ t * (b / 2) :=
    mul_le_mul_of_nonneg_left hbracket ht0
  have n1 := neg_abs_le (B.sigmaInt h ν S (fun x => ∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν))
  have n2 := neg_abs_le (∫ x in Set.Icc (0 : ℝ) 2 \ S, B.sigmaInt h ν S (fun y => B.contKernel h x y) ∂ν)
  have n3 := neg_abs_le (∫ x in Set.Icc (0 : ℝ) 2 \ S,
    (∫ y in Set.Icc (0 : ℝ) 2 \ S, B.contKernel h x y ∂ν) ∂ν)
  nlinarith [hcentralB, hΨ, hexp, hsplitQ, hloss, hlossb]

/-- **`lem:auxiliary-lagrangian-bound`, measure-level form.**  There are `ρ₀ > 0` and
`ρ ↦ b_ρ > 0` on `(0, ρ₀)`, chosen before the graph data, such that for `m > 0` and `v = n ≥ 2`
with `2m = nd` there is `C_{d,m} ≥ 1` with: for every `0 < ρ < ρ₀` and `K ≥ 0` there is
`0 < h_ρ ≤ h₀` such that for all `0 < h < h_ρ` and every probability measure `ν` on `[0,2]`
satisfying `∫|x - u_h|^{1/2}dν ≤ Kh^{1/2}` and `ν(𝒯_ρ) ≤ Kh⁴`,

`(a/2) A_{h,ρ}(ν) + (b_ρ/2) ν(𝒯_ρ) - C_{d,m} Δ_h(ν)² ≤ 𝓛_h(ν) - 𝓛_h(ν_h)`,   `a = d³/24`.

`C_{d,m}` does not depend on `ρ` or `K`; `ρ₀` and `b_ρ` depend on neither `(n, m)` nor `K`. -/
theorem auxiliary_lagrangian_bound_law (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ b : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → 0 < b ρ) ∧
      ∀ {n : ℕ} {m : ℝ}, 0 < m → 2 * m = (n : ℝ) * (d : ℝ) → 2 ≤ n →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∀ K : ℝ, 0 ≤ K →
        ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧ ∀ h : ℝ, 0 < h → h < hρ →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
          (∫ x, Real.sqrt |x - B.u h| ∂ν) ≤ K * Real.sqrt h →
          (ν (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal ≤ K * h ^ 4 →
          (d : ℝ) ^ 3 / 24 / 2 * (∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂ν)
              + b ρ / 2 * (ν (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
              - C * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2
            ≤ B.auxLagrangian m n h ν - B.auxLagrangian m n h (B.distributionMeasure h) := by
  obtain ⟨ρ₀, Cc, hρ₀, hCc1, hgap⟩ := auxiliary_gap_bound_law hd B
  choose! b hb0 hgapb using hgap
  refine ⟨ρ₀, hρ₀, b, hb0, ?_⟩
  intro n m hm hn hn2
  obtain ⟨Cμ, δμ, hCμ, hδμ, hμbd⟩ := B.exists_abs_muVal_le hm
  obtain ⟨CT, hCT⟩ : ∃ CT : ℝ, CT = Cμ * ((n : ℝ) ^ 2 * (2 ^ d) ^ (2 * n)) := ⟨_, rfl⟩
  have hCT0 : 0 ≤ CT := by rw [hCT]; positivity
  refine ⟨Cc + CT, by linarith, fun ρ hρ0 hρlt K hK => ?_⟩
  obtain ⟨hρ, hρ0', hρle, hgapK⟩ := hgapb ρ hρ0 hρlt K hK
  refine ⟨min hρ δμ, lt_min hρ0' hδμ, le_trans (min_le_left _ _) hρle, ?_⟩
  intro h hpos hlt ν hνprob hν hI htail
  have hhB : |h| < B.h₀ := by
    rw [abs_of_pos hpos]; exact lt_of_lt_of_le hlt (le_trans (min_le_left _ _) hρle)
  have hμ := hμbd h (by rw [abs_of_pos hpos]; exact lt_of_lt_of_le hlt (min_le_right _ _))
  have h1 := hgapK h hpos (lt_of_lt_of_le hlt (min_le_left _ _)) ν hνprob hν hI htail
  have h2 := KKTFamily.auxLagrangian_gap_ge hd B hhB hm hn hn2 hν
  have hsq : 0 ≤ (n : ℝ) ^ 2 * (2 ^ d) ^ (2 * n) * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2 := by
    positivity
  have h3 : |B.muVal m h| * ((n : ℝ) ^ 2 * (2 ^ d) ^ (2 * n) * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2)
      ≤ CT * ((∫ x, x ^ d ∂ν) - B.qVal h) ^ 2 := by
    rw [hCT]
    have := mul_le_mul_of_nonneg_right hμ hsq
    linarith
  linarith

end SingularEndpoint

end UpperTailOptimizers
