import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangianBound
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne

/-!
# `lem:auxiliary-lagrangian-bound` and `lem:graphon-lagrangian-bound` for the decomposition

Both lemmas (`paper/sections/singular_auxiliary_lagrangian.tex`,
`paper/sections/singular_graphon_comparison.tex`) are stated for `0 < h < h_ρ`, a graphon `W`
satisfying the hypotheses of `lem:localization-rank-one`, the decomposition `W = f ⊗ f + E`
provided there, and `ν` the law of `f`.  The sets are the paper's: the open window
`𝒩_ρ = openWindow d ρ` and the closed tail `𝒯_ρ = [0,2] ∖ 𝒩_ρ`;
`A_{h,ρ}(ν) = ∫_{𝒩_ρ} Q_h² dν` and `Δ_h(ν) = m_d(ν) - q_h`.

Each lemma comes in two forms.

* The `_of_close` form holds for **every** factor decomposition with `‖f - u_*‖₄ ≤ K₀h` (and,
  for `lem:graphon-lagrangian-bound`, `‖E‖₂ ≤ K₀h`), for every `K₀ ≥ 0`; `h_ρ` is chosen after
  `K₀`.
* The paper form (`auxiliary_lagrangian_bound`, `graphon_lagrangian_bound`) composes it with
  `localization_rank_one_reduction` (`K₀ = C_d`): for every feasible `W` with
  `I_{p_h}(W) ≤ I_{p_h}(W_h)` it returns the decomposition of `lem:localization-rank-one`,
  with all of that lemma's properties, together with the estimate.

The constants are chosen in the order of the paper, and their subscripts are respected:
`ρ₀`, `a = d³/24`, `ρ ↦ b_ρ` and `ρ ↦ C_{d,ρ}` come before the graph; `C_{d,m}` comes after the
graph but before `ρ`; `h_ρ` comes last.

## `lem:graphon-lagrangian-bound`

The proof is the paper's assembly.  `comparison_splitting` and `comparisonMain_entropy_split`
give

`I_{p_h}(W) - I_{p_h}(W_h) = [𝒥_h(ν) - 𝒥_h(ν_h)] + central + 2·mixed + tail–tail`,

and `muVal_tDensity_le_etaVal` converts `μ_h{t(H,W) - r_h^m}` into `η_hΔ` plus
`|μ_h|{v²(2^d)^{2v}Δ² + 40^m‖E‖₂³}`.  The law half is `auxiliary_gap_bound_law` at the open
radius `ρ`.  The three residual halves are the existing estimates at the **closed** radius `ρ/2`:
`comparisonMain_exists_central_bound` (with the KKT smallness `θ = min(1, d³/192)`),
`rowJensen_exists_mixed` and `rowJensen_exists_tailSq`; the residual norm is split by
`comparisonMain_residSq_split`, `mixed_resid_le` and `comparisonMain_tailSq_resid_le`.  The closed
window at `ρ/2` lies inside the open window at `ρ` (`setIntegral_centralSet_half_le`), and the
rows with `ρ/2 < |f - u_*| < ρ` are charged to `A_{h,ρ}(ν)`, because `Q_h² ≥ (ρ/4)⁴` there
(`tailMass_half_le`).  The graph enters only through `μ_h` and `t(H,W)`, which is why `C_{d,ρ}`
does not depend on it.
-/

universe u

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## The a-priori quantities of the law of `f` -/

/-- `√z ≤ r + z⁴/r⁷` for `z ≥ 0` and `r > 0`. -/
theorem sqrt_le_add_pow_div {z r : ℝ} (hz : 0 ≤ z) (hr : 0 < r) :
    Real.sqrt z ≤ r + z ^ 4 / r ^ 7 := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt z := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg z
  have hzs : z = s ^ 2 := by rw [hs, Real.sq_sqrt hz]
  rw [← hs, hzs]
  have hq : 0 ≤ (s ^ 2) ^ 4 / r ^ 7 := by positivity
  rcases le_or_gt s r with hle | hgt
  · linarith
  · have hs7 : r ^ 7 ≤ s ^ 7 := pow_le_pow_left₀ hr.le hgt.le 7
    have hkey : s ≤ (s ^ 2) ^ 4 / r ^ 7 := by
      rw [le_div_iff₀ (by positivity)]
      calc s * r ^ 7 ≤ s * s ^ 7 := mul_le_mul_of_nonneg_left hs7 hs0
        _ = (s ^ 2) ^ 4 := by ring
    linarith

/-- **`∫|x - u|^{1/2} d(law f) ≤ (9 + 8K₀⁴)h^{1/2}`** when `‖f - u_*‖₄ ≤ K₀h` and
`|u - u_*| ≤ h`. -/
theorem integral_sqrt_abs_sub_le {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) {h K₀ u : ℝ} (hh : 0 < h)
    (hL : Lnorm unitμ 4 (fun x => f x - uStar d) ≤ K₀ * h) (hu : |u - uStar d| ≤ h) :
    ∫ x, Real.sqrt |x - u| ∂(comparisonDistribution f) ≤ (9 + 8 * K₀ ^ 4) * Real.sqrt h := by
  have hmeas : Measurable fun x : ℝ => Real.sqrt |x - u| := by fun_prop
  rw [comparison_integral hf hmeas]
  have hr : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have h4 := integral_pow_four_le_of_Lnorm hL
  have hbdf : ∀ x, |f x| ≤ 2 := fun x => abs_le.mpr ⟨by linarith [hnn x], hbd x⟩
  have hi1 : Integrable (fun x => Real.sqrt |f x - u|) unitμ := by
    refine Integrable.of_bound (hmeas.comp hf).aestronglyMeasurable (Real.sqrt (2 + |u|))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (le_trans (abs_sub _ _) (by linarith [hbdf x]))
  have hi2 : Integrable (fun x => (f x - uStar d) ^ 4) unitμ := by
    refine Integrable.of_bound ((hf.sub measurable_const).pow_const 4).aestronglyMeasurable
      ((2 + |uStar d|) ^ 4) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_trans (abs_sub _ _) (by linarith [hbdf x])) 4
  have hpt : ∀ x, Real.sqrt |f x - u|
      ≤ (Real.sqrt h + 8 * h ^ 4 / Real.sqrt h ^ 7)
        + 8 / Real.sqrt h ^ 7 * (f x - uStar d) ^ 4 := by
    intro x
    have h1 := sqrt_le_add_pow_div (abs_nonneg (f x - u)) hr
    have h2 : |f x - u| ^ 4 ≤ 8 * (f x - uStar d) ^ 4 + 8 * h ^ 4 := by
      have e : |f x - u| ^ 4 = (f x - u) ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      have hu4 : (u - uStar d) ^ 4 ≤ h ^ 4 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hu 4
        rwa [← abs_pow, abs_of_nonneg (by positivity)] at this
      rw [e]
      nlinarith [sq_nonneg ((f x - uStar d) - (u - uStar d)),
        sq_nonneg ((f x - uStar d) + (u - uStar d)), sq_nonneg (f x - uStar d),
        sq_nonneg (u - uStar d)]
    have h3 : |f x - u| ^ 4 / Real.sqrt h ^ 7
        ≤ (8 * (f x - uStar d) ^ 4 + 8 * h ^ 4) / Real.sqrt h ^ 7 :=
      div_le_div_of_nonneg_right h2 (by positivity)
    have e2 : (8 * (f x - uStar d) ^ 4 + 8 * h ^ 4) / Real.sqrt h ^ 7
        = 8 * h ^ 4 / Real.sqrt h ^ 7 + 8 / Real.sqrt h ^ 7 * (f x - uStar d) ^ 4 := by ring
    linarith
  have hint3 : Integrable (fun x => (Real.sqrt h + 8 * h ^ 4 / Real.sqrt h ^ 7)
      + 8 / Real.sqrt h ^ 7 * (f x - uStar d) ^ 4) unitμ :=
    (integrable_const _).add (hi2.const_mul _)
  have hmono := integral_mono hi1 hint3 hpt
  have heval : ∫ x, ((Real.sqrt h + 8 * h ^ 4 / Real.sqrt h ^ 7)
        + 8 / Real.sqrt h ^ 7 * (f x - uStar d) ^ 4) ∂unitμ
      = (Real.sqrt h + 8 * h ^ 4 / Real.sqrt h ^ 7)
        + 8 / Real.sqrt h ^ 7 * ∫ x, (f x - uStar d) ^ 4 ∂unitμ := by
    rw [integral_add (integrable_const _) (hi2.const_mul _), integral_const_mul,
      integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hh4 : h ^ 4 = Real.sqrt h ^ 8 := by
    rw [show Real.sqrt h ^ 8 = (Real.sqrt h ^ 2) ^ 4 by ring, Real.sq_sqrt hh.le]
  have hbound : 8 * h ^ 4 / Real.sqrt h ^ 7
        + 8 / Real.sqrt h ^ 7 * ∫ x, (f x - uStar d) ^ 4 ∂unitμ
      ≤ (8 * K₀ ^ 4 + 8) * Real.sqrt h := by
    have e : 8 * h ^ 4 / Real.sqrt h ^ 7 + 8 / Real.sqrt h ^ 7 * ∫ x, (f x - uStar d) ^ 4 ∂unitμ
        = (8 * (∫ x, (f x - uStar d) ^ 4 ∂unitμ) + 8 * h ^ 4) / Real.sqrt h ^ 7 := by ring
    rw [e, div_le_iff₀ (by positivity)]
    have h5 : 8 * (∫ x, (f x - uStar d) ^ 4 ∂unitμ) + 8 * h ^ 4 ≤ (8 * K₀ ^ 4 + 8) * h ^ 4 := by
      have : (K₀ * h) ^ 4 = K₀ ^ 4 * h ^ 4 := by ring
      nlinarith [h4]
    calc 8 * (∫ x, (f x - uStar d) ^ 4 ∂unitμ) + 8 * h ^ 4 ≤ (8 * K₀ ^ 4 + 8) * h ^ 4 := h5
      _ = (8 * K₀ ^ 4 + 8) * Real.sqrt h * Real.sqrt h ^ 7 := by rw [hh4]; ring
  rw [heval] at hmono
  linarith

/-- **Chebyshev on the open window**: `λ{f ∉ 𝒩_ρ} ≤ ∫(f - u_*)⁴/ρ⁴`. -/
theorem tail_openWindow_le {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) {ρ c : ℝ} (hρ : 0 < ρ)
    (hc : ∫ x, (f x - uStar d) ^ 4 ∂unitμ ≤ c) :
    (comparisonDistribution f (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal ≤ c / ρ ^ 4 := by
  rw [comparison_distribution_diff hf hnn hbd (measurableSet_openWindow d ρ)]
  have hbdf : ∀ x, |f x| ≤ 2 := fun x => abs_le.mpr ⟨by linarith [hnn x], hbd x⟩
  have hi2 : Integrable (fun x => (f x - uStar d) ^ 4) unitμ := by
    refine Integrable.of_bound ((hf.sub measurable_const).pow_const 4).aestronglyMeasurable
      ((2 + |uStar d|) ^ 4) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_trans (abs_sub _ _) (by linarith [hbdf x])) 4
  have hcheb := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => by positivity : 0 ≤ᵐ[unitμ] fun x => (f x - uStar d) ^ 4)
    hi2 (ρ ^ 4)
  have hsub : {x | f x ∉ openWindow d ρ} ⊆ {x | ρ ^ 4 ≤ (f x - uStar d) ^ 4} := by
    intro x hx
    have hx' : ¬ (uStar d - ρ < f x ∧ f x < uStar d + ρ) := hx
    have habs : ρ ≤ |f x - uStar d| := by
      by_contra hcon
      exact hx' ⟨by linarith [(abs_lt.mp (not_le.mp hcon)).1],
        by linarith [(abs_lt.mp (not_le.mp hcon)).2]⟩
    have := pow_le_pow_left₀ hρ.le habs 4
    show ρ ^ 4 ≤ (f x - uStar d) ^ 4
    rwa [← abs_pow, abs_of_nonneg (by positivity)] at this
  have hmono : unitμ.real {x | f x ∉ openWindow d ρ}
      ≤ unitμ.real {x | ρ ^ 4 ≤ (f x - uStar d) ^ 4} :=
    measureReal_mono hsub
  rw [le_div_iff₀ (by positivity), ← measureReal_def]
  nlinarith [hcheb, hmono, pow_pos hρ 4]

/-- The two a-priori quantities of `auxiliary_gap_bound_law` for the law of `f`, with the
single constant `K = 9 + 8K₀⁴ + K₀⁴/ρ⁴`, from `‖f - u_*‖₄ ≤ K₀h` and `|u - u_*| ≤ h`. -/
theorem law_apriori_le {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) {h K₀ u ρ : ℝ} (hh : 0 < h) (hρ : 0 < ρ)
    (hL : Lnorm unitμ 4 (fun x => f x - uStar d) ≤ K₀ * h) (hu : |u - uStar d| ≤ h) :
    (∫ x, Real.sqrt |x - u| ∂(comparisonDistribution f))
        ≤ ((9 + 8 * K₀ ^ 4) + K₀ ^ 4 / ρ ^ 4) * Real.sqrt h ∧
      (comparisonDistribution f (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
        ≤ ((9 + 8 * K₀ ^ 4) + K₀ ^ 4 / ρ ^ 4) * h ^ 4 := by
  constructor
  · refine le_trans (integral_sqrt_abs_sub_le hf hnn hbd hh hL hu)
      (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    have : 0 ≤ K₀ ^ 4 / ρ ^ 4 := by positivity
    linarith
  · refine le_trans (tail_openWindow_le hf hnn hbd hρ (integral_pow_four_le_of_Lnorm hL)) ?_
    rw [show (K₀ * h) ^ 4 / ρ ^ 4 = K₀ ^ 4 / ρ ^ 4 * h ^ 4 by ring]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ 8 * K₀ ^ 4 := by positivity
    linarith

/-- A `d`-regular graph with `d ≥ 2` and an edge has at least two vertices. -/
private theorem graphonLagrangian_two_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) : 2 ≤ Fintype.card V := by
  have hhand : 2 * H.edgeFinset.card = Fintype.card V * d :=
    factorMain_two_mul_card_edgeFinset H hreg
  have hdm : d ≤ H.edgeFinset.card := degree_le_card_edges H hreg hm
  nlinarith [hhand, hdm, hm, hd]

/-! ## `lem:auxiliary-lagrangian-bound` -/

/-- **`lem:auxiliary-lagrangian-bound` for every decomposition close to `u_*`.**  There are
`ρ₀ > 0` and `ρ ↦ b_ρ > 0` such that for `m > 0` and `v = n ≥ 2` with `2m = nd` there is
`C_{d,m} ≥ 1` with: for every `0 < ρ < ρ₀` and `K₀ ≥ 0` there is `0 < h_ρ ≤ h₀` such that for
all `0 < h < h_ρ`, every graphon `W` and every decomposition `W = f ⊗ f + E` with
`‖f - u_*‖₄ ≤ K₀h`, and `ν` the law of `f`,

`(a/2) A_{h,ρ}(ν) + (b_ρ/2) ν(𝒯_ρ) - C_{d,m} Δ_h(ν)² ≤ 𝓛_h(ν) - 𝓛_h(ν_h)`,   `a = d³/24`. -/
theorem auxiliary_lagrangian_bound_of_close (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ b : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → 0 < b ρ) ∧
      ∀ {n : ℕ} {m : ℝ}, 0 < m → 2 * m = (n : ℝ) * (d : ℝ) → 2 ≤ n →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∀ K₀ : ℝ, 0 ≤ K₀ →
        ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧ ∀ h : ℝ, 0 < h → h < hρ →
        ∀ (W : Graphon) (P : FactorDecomp d W),
          Lnorm unitμ 4 (fun x => P.f x - uStar d) ≤ K₀ * h →
          (d : ℝ) ^ 3 / 24 / 2
                * (∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂(comparisonDistribution P.f))
              + b ρ / 2
                * (comparisonDistribution P.f (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
              - C * ((∫ x, x ^ d ∂(comparisonDistribution P.f)) - B.qVal h) ^ 2
            ≤ B.auxLagrangian m n h (comparisonDistribution P.f)
                - B.auxLagrangian m n h (B.distributionMeasure h) := by
  obtain ⟨ρ₀, hρ₀, b, hb0, hlaw⟩ := auxiliary_lagrangian_bound_law hd B
  refine ⟨ρ₀, hρ₀, b, hb0, ?_⟩
  intro n m hm hn hn2
  obtain ⟨C, hC1, hlawC⟩ := hlaw hm hn hn2
  refine ⟨C, hC1, fun ρ hρ0 hρlt K₀ hK₀ => ?_⟩
  obtain ⟨hL, hL0, hLle, hlawK⟩ :=
    hlawC ρ hρ0 hρlt ((9 + 8 * K₀ ^ 4) + K₀ ^ 4 / ρ ^ 4) (by positivity)
  obtain ⟨δu, hδu, hu⟩ := exists_abs_u_sub_le B
  refine ⟨min hL δu, lt_min hL0 hδu, le_trans (min_le_left _ _) hLle, ?_⟩
  intro h hpos hlt W P hclose
  obtain ⟨hI, hT⟩ := law_apriori_le P.meas_f P.f_nonneg P.f_bdd hpos hρ0 hclose
    (hu h hpos (lt_of_lt_of_le hlt (min_le_right _ _)))
  exact hlawK h hpos (lt_of_lt_of_le hlt (min_le_left _ _)) _
    (comparison_isProbabilityMeasure P.meas_f)
    (comparison_distribution_compl_Icc P.meas_f P.f_nonneg P.f_bdd) hI hT

/-- **`lem:auxiliary-lagrangian-bound`.**  Let `C_d` be the constant of
`lem:localization-rank-one`.  There are `ρ₀ > 0` and `ρ ↦ b_ρ > 0` on `(0, ρ₀)` such that for
every `d`-regular graph `H` with `m ≥ 1` edges and `v` vertices there is `C_{d,m} ≥ 1` with: for
every `0 < ρ < ρ₀` there is `0 < h_ρ ≤ h₀` such that for all `0 < h < h_ρ` and every graphon `W`
with `t(H,W) ≥ r_h^m` and `I_{p_h}(W) ≤ I_{p_h}(W_h)`, the decomposition `W = f ⊗ f + E` of
`lem:localization-rank-one` (with all its properties) satisfies, for `ν` the law of `f`,

`𝓛_h(ν) - 𝓛_h(ν_h) = 𝒥_h(ν) - 𝒥_h(ν_h) - μ_h{m_d(ν)^v - q_h^v}
  ≥ (a/2) A_{h,ρ}(ν) + (b_ρ/2) ν(𝒯_ρ) - C_{d,m} Δ_h(ν)²`,   `a = d³/24`. -/
theorem auxiliary_lagrangian_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C₀ : ℝ, 1 < C₀ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ b : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → 0 < b ρ) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ v, H.degree v = d) → 1 ≤ H.edgeFinset.card →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
          ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧
            ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < hρ →
            ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
              W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
              ∃ P : FactorDecomp d W,
                ((∀ x y, W.toFun x y = P.f x * P.f y + P.resid x y) ∧
                  MemLp P.f d unitμ ∧ MemLp (fun z : ℝ × ℝ => P.resid z.1 z.2) 2 gμ ∧
                  (∀ᵐ x ∂unitμ, kernelOp W.toFun (fun y => P.f y ^ (d - 1)) x = P.qVal * P.f x) ∧
                  (∀ᵐ x ∂unitμ, kernelOp P.resid (fun y => P.f y ^ (d - 1)) x = 0) ∧
                  0 < P.qVal ∧ (∀ x, 0 ≤ P.f x ∧ P.f x ≤ 2) ∧
                  Lnorm unitμ 4 (fun x => P.f x - uStar d) ≤ C₀ * h ∧
                  P.residNorm ≤ C₀ * h ∧
                  |P.qVal - B.qVal h| ≤ C₀ * h ^ 2 ∧
                  |W.tDensity H - P.qVal ^ Fintype.card V|
                    ≤ (40 : ℝ) ^ H.edgeFinset.card * P.residNorm ^ 3) ∧
                B.auxLagrangian (H.edgeFinset.card : ℝ) (Fintype.card V) h
                      (comparisonDistribution P.f)
                    - B.auxLagrangian (H.edgeFinset.card : ℝ) (Fintype.card V) h
                      (B.distributionMeasure h)
                  = B.distributionJ h (comparisonDistribution P.f)
                      - B.distributionJ h (B.distributionMeasure h)
                    - B.muVal (H.edgeFinset.card : ℝ) h
                      * ((∫ x, x ^ d ∂(comparisonDistribution P.f)) ^ Fintype.card V
                        - B.qVal h ^ Fintype.card V) ∧
                (d : ℝ) ^ 3 / 24 / 2
                      * (∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂(comparisonDistribution P.f))
                    + b ρ / 2
                      * (comparisonDistribution P.f (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
                    - C * ((∫ x, x ^ d ∂(comparisonDistribution P.f)) - B.qVal h) ^ 2
                  ≤ B.auxLagrangian (H.edgeFinset.card : ℝ) (Fintype.card V) h
                      (comparisonDistribution P.f)
                    - B.auxLagrangian (H.edgeFinset.card : ℝ) (Fintype.card V) h
                      (B.distributionMeasure h) := by
  obtain ⟨C₀, hC₀, h₀, hh₀, -, hloc⟩ := localization_rank_one_reduction hd B
  obtain ⟨ρ₀, hρ₀, b, hb0, hgen⟩ := auxiliary_lagrangian_bound_of_close hd B
  refine ⟨C₀, hC₀, ρ₀, hρ₀, b, hb0, ?_⟩
  intro V _ _ H _ hreg hcard
  have hv := graphonLagrangian_two_le_card H hd hreg hcard
  have hmpos : (0 : ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hcard
  have hnR : 2 * (H.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) * (d : ℝ) := by
    have := factorMain_two_mul_card_edgeFinset H hreg
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  obtain ⟨C, hC1, hgenC⟩ := hgen hmpos hnR hv
  refine ⟨C, hC1, fun ρ hρ0 hρlt => ?_⟩
  obtain ⟨hρ, hρ0', hρle, hbound⟩ := hgenC ρ hρ0 hρlt C₀ (by linarith)
  refine ⟨min hρ h₀, lt_min hρ0' hh₀, le_trans (min_le_left _ _) hρle, ?_⟩
  intro h hh hpos hlt W hfeas hcost
  obtain ⟨-, P, hP⟩ :=
    hloc H hreg hcard h hh hpos (lt_of_lt_of_le hlt (min_le_right _ _)) W hfeas hcost
  refine ⟨P, hP, ?_, hbound h hpos (lt_of_lt_of_le hlt (min_le_left _ _)) W P
    hP.2.2.2.2.2.2.2.1⟩
  rw [KKTFamily.auxLagrangian_distributionMeasure B hh, KKTFamily.auxLagrangian]
  ring

/-! ## `lem:graphon-lagrangian-bound` -/

/-- `Q_h²` is measurable. -/
theorem measurable_Qh_sq (B : KKTFamily d) (h : ℝ) : Measurable fun x : ℝ => B.Qh h x ^ 2 := by
  have hm : Measurable fun x : ℝ => ((x - B.sVal h) * (x - B.tVal h)) ^ 2 :=
    ((measurable_id.sub measurable_const).mul (measurable_id.sub measurable_const)).pow_const 2
  exact hm

/-- `Q_h(f)²` is integrable for `f` valued in `[0,2]`. -/
theorem integrable_Qh_comp_sq {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) (B : KKTFamily d) (h : ℝ) :
    Integrable (fun x => B.Qh h (f x) ^ 2) unitμ := by
  refine Integrable.of_bound ((measurable_Qh_sq B h).comp hf).aestronglyMeasurable
    (16 * (2 + |uStar d|) ^ 4 + 16 * (B.u h - uStar d) ^ 4 + 2 * h ^ 4)
    (Filter.Eventually.of_forall fun x => ?_)
  show ‖B.Qh h (f x) ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := sq_Qh_le B h (f x)
  have h2 : |f x - uStar d| ≤ 2 + |uStar d| :=
    le_trans (abs_sub _ _) (by rw [abs_of_nonneg (hnn x)]; linarith [hbd x])
  have h3 : (f x - uStar d) ^ 4 ≤ (2 + |uStar d|) ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h2 4
    rwa [← abs_pow, abs_of_nonneg (by positivity)] at this
  linarith

/-- **`Q_h(x)² ≥ (ρ/4)⁴` off the closed window of radius `ρ/2`**, once
`|u_h - u_*| ≤ h ≤ ρ/8`. -/
theorem Qh_sq_ge_of_far (B : KKTFamily d) {h ρ x : ℝ} (hρ : 0 < ρ) (hh0 : 0 ≤ h)
    (hhρ : h ≤ ρ / 8) (hu : |B.u h - uStar d| ≤ h) (hx : ρ / 2 < |x - uStar d|) :
    (ρ / 4) ^ 4 ≤ B.Qh h x ^ 2 := by
  have h1 : 3 * ρ / 8 ≤ |x - B.u h| := by
    have := abs_sub_abs_le_abs_sub (x - uStar d) (B.u h - uStar d)
    rw [show x - uStar d - (B.u h - uStar d) = x - B.u h by ring] at this
    linarith
  have h2 : (3 * ρ / 8) ^ 2 ≤ (x - B.u h) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    rwa [sq_abs] at this
  have h3 : h ^ 2 ≤ (ρ / 8) ^ 2 := pow_le_pow_left₀ hh0 hhρ 2
  have hQ : ρ ^ 2 / 8 ≤ B.Qh h x := by
    rw [Qh_eq_sq_sub]
    nlinarith
  have hQ0 : 0 ≤ ρ ^ 2 / 8 := by positivity
  have e1 : (ρ / 4) ^ 4 = ρ ^ 4 / 256 := by ring
  have e2 : (ρ ^ 2 / 8) ^ 2 = ρ ^ 4 / 64 := by ring
  have h4 : ρ ^ 4 / 256 ≤ ρ ^ 4 / 64 := by
    have := pow_pos hρ 4
    linarith
  calc (ρ / 4) ^ 4 ≤ (ρ ^ 2 / 8) ^ 2 := by rw [e1, e2]; exact h4
    _ ≤ B.Qh h x ^ 2 := pow_le_pow_left₀ hQ0 hQ 2

/-- **The closed window at `ρ/2` inside the open window at `ρ`**:
`∫_{f ∈ 𝒩_{ρ/2}^{cl}} Q_h(f)² ≤ ∫_{f ∈ 𝒩_ρ} Q_h(f)²`. -/
theorem setIntegral_centralSet_half_le {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) (B : KKTFamily d) (h : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ x in centralSet d (ρ / 2) f, B.Qh h (f x) ^ 2 ∂unitμ)
      ≤ ∫ x in {x | f x ∈ openWindow d ρ}, B.Qh h (f x) ^ 2 ∂unitμ := by
  refine setIntegral_mono_set (integrable_Qh_comp_sq hf hnn hbd B h).integrableOn
    (Filter.Eventually.of_forall fun x => sq_nonneg _) (LE.le.eventuallyLE ?_)
  intro x hx
  have hx' : |f x - uStar d| ≤ ρ / 2 := (factorTail_mem_centralWindow_iff d (ρ / 2) (f x)).mp hx
  have hb := abs_le.mp hx'
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- **The annulus bound**: the rows outside the closed window at `ρ/2` are either outside the
open window at `ρ`, or in the annulus, where `Q_h² ≥ (ρ/4)⁴`:

`λ{f ∉ 𝒩_{ρ/2}^{cl}} ≤ λ{f ∉ 𝒩_ρ} + (4/ρ)⁴ ∫_{f ∈ 𝒩_ρ} Q_h(f)²`. -/
theorem tailMass_half_le {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) (B : KKTFamily d) {h ρ : ℝ} (hρ : 0 < ρ) (hh0 : 0 ≤ h)
    (hhρ : h ≤ ρ / 8) (hu : |B.u h - uStar d| ≤ h) :
    tailMass d (ρ / 2) f
      ≤ (unitμ {x | f x ∉ openWindow d ρ}).toReal
        + (4 / ρ) ^ 4 * ∫ x in {x | f x ∈ openWindow d ρ}, B.Qh h (f x) ^ 2 ∂unitμ := by
  have hmO : MeasurableSet {x | f x ∈ openWindow d ρ} := hf (measurableSet_openWindow d ρ)
  have hmC : MeasurableSet (centralSet d (ρ / 2) f) := measurableSet_centralSet hf d (ρ / 2)
  have hmS₂ : MeasurableSet ({x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ) :=
    hmO.inter hmC.compl
  have hsub : (centralSet d (ρ / 2) f)ᶜ
      ⊆ {x | f x ∉ openWindow d ρ} ∪ ({x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ) := by
    intro x hx
    by_cases hxo : f x ∈ openWindow d ρ
    · exact Or.inr ⟨hxo, hx⟩
    · exact Or.inl hxo
  have hmeas1 : unitμ.real (centralSet d (ρ / 2) f)ᶜ
      ≤ unitμ.real {x | f x ∉ openWindow d ρ}
        + unitμ.real ({x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ) :=
    le_trans (measureReal_mono hsub) (measureReal_union_le _ _)
  have hQint := integrable_Qh_comp_sq hf hnn hbd B h
  have hpt : ∀ x ∈ {x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ,
      (ρ / 4) ^ 4 ≤ B.Qh h (f x) ^ 2 := by
    intro x hx
    refine Qh_sq_ge_of_far B hρ hh0 hhρ hu ?_
    have hx2 : ¬ f x ∈ centralWindow d (ρ / 2) := hx.2
    rw [factorTail_mem_centralWindow_iff] at hx2
    exact not_le.mp hx2
  have hlow : unitμ.real ({x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ) * (ρ / 4) ^ 4
      ≤ ∫ x in {x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ,
          B.Qh h (f x) ^ 2 ∂unitμ := by
    have h1 := setIntegral_mono_on (integrable_const ((ρ / 4) ^ 4)).integrableOn
      hQint.integrableOn hmS₂ hpt
    rwa [setIntegral_const, smul_eq_mul] at h1
  have hup : (∫ x in {x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ,
        B.Qh h (f x) ^ 2 ∂unitμ)
      ≤ ∫ x in {x | f x ∈ openWindow d ρ}, B.Qh h (f x) ^ 2 ∂unitμ :=
    setIntegral_mono_set hQint.integrableOn (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (LE.le.eventuallyLE Set.inter_subset_left)
  have hκ : (4 / ρ) ^ 4 * (ρ / 4) ^ 4 = 1 := by
    field_simp
  have hS₂le : unitμ.real ({x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ)
      ≤ (4 / ρ) ^ 4 * ∫ x in {x | f x ∈ openWindow d ρ}, B.Qh h (f x) ^ 2 ∂unitμ := by
    have hκ0 : 0 ≤ (4 / ρ) ^ 4 := by positivity
    have h1 := mul_le_mul_of_nonneg_left (le_trans hlow hup) hκ0
    have e : (4 / ρ) ^ 4
          * (unitμ.real ({x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ) * (ρ / 4) ^ 4)
        = unitμ.real ({x | f x ∈ openWindow d ρ} ∩ (centralSet d (ρ / 2) f)ᶜ) := by
      rw [mul_comm, mul_assoc, mul_comm ((ρ / 4) ^ 4), hκ, mul_one]
    linarith
  show unitμ.real (centralSet d (ρ / 2) f)ᶜ ≤ unitμ.real {x | f x ∉ openWindow d ρ} + _
  linarith

/-- `p h ≤ t` from `h ≤ t/(p + 1)`, for `p, h ≥ 0`. -/
private theorem graphonLagrangian_mul_le {p h t : ℝ} (hp : 0 ≤ p) (hh : 0 ≤ h)
    (hle : h ≤ t / (p + 1)) : p * h ≤ t := by
  have h1 : h * (p + 1) ≤ t := (le_div_iff₀ (by linarith)).mp hle
  linarith

/-- **The arithmetic of `lem:graphon-lagrangian-bound`.**  The estimates of the proof, with every
integral replaced by a real number: the splitting (`hsplit`, `hent`), the law half (`hlaw`), the
central square, mixed rectangles and tail–tail square at the closed radius (`hc`, `hr`, `hk`), the
graph term (`hlag`, `hμ`), the three-way split of `‖E‖₂²` (`hresid`, `hmixres`, `hcor`), the
annulus (`hann`), and the smallness of the error coefficients (`hsm1`–`hsm3`). -/
private theorem graphonLagrangian_algebra
    {Iw Ih Jn Jh Ent Ec Em Et η μ mabs tW rm A T A' ε X Mx Cr L R Δ a2 θ α b C₁ CC CK Cμ N P40
      τ κ c Ci : ℝ}
    (hsplit : Iw - Ih = (Jn - Jh) + Ent)
    (hent : Ent = Ec + 2 * Em + Et)
    (hlaw : a2 * A + b / 2 * T - C₁ * Δ ^ 2 ≤ Jn - Jh - η * Δ)
    (hc : 2 * X - θ * (A' + X) - CC * (ε * L) ≤ Ec)
    (hr : -(τ / 3 * ε) ≤ 2 * Em)
    (hk : -(CK * ε ^ 2) ≤ Et)
    (hlag : μ * (tW - rm) ≤ η * Δ + mabs * (N * Δ ^ 2 + P40 * L ^ 3))
    (hμ : mabs ≤ Cμ)
    (hresid : R = X + 2 * Mx + Cr) (hmixres : Mx ≤ 25 * ε) (hcor : Cr ≤ 25 * ε ^ 2)
    (hann : ε ≤ T + κ * A) (hA'A : A' ≤ A)
    (hA0 : 0 ≤ A) (hT0 : 0 ≤ T) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hX0 : 0 ≤ X) (hL0 : 0 ≤ L)
    (hR0 : 0 ≤ R) (hLR : L ^ 2 = R) (hN0 : 0 ≤ N) (hP40 : 0 ≤ P40)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα : α = a2 - θ)
    (hτ0 : 0 < τ) (hτb : τ ≤ b / 4) (hτκ : τ * κ ≤ α / 2) (hκ0 : 0 < κ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hcτ : c ≤ τ / 150)
    (hsm1 : CC * L ≤ τ / 3) (hsm2 : CK * ε ≤ τ / 3) (hsm3 : Cμ * P40 * L ≤ c / 2)
    (hCα : Ci ≤ α / 4) (hCb : Ci ≤ b / 8) (hCc : Ci ≤ c / 2) :
    Ci * (A + T + R) - (C₁ + Cμ * N) * Δ ^ 2 ≤ Iw - Ih - μ * (tW - rm) := by
  have l1 : θ * A' ≤ θ * A := mul_le_mul_of_nonneg_left hA'A hθ0.le
  have l2 : θ * X ≤ X := by
    have := mul_le_mul_of_nonneg_right hθ1 hX0
    linarith
  have l3 : CC * (ε * L) ≤ τ / 3 * ε := by
    have := mul_le_mul_of_nonneg_left hsm1 hε0
    linarith
  have l4 : CK * ε ^ 2 ≤ τ / 3 * ε := by
    have := mul_le_mul_of_nonneg_left hsm2 hε0
    linarith
  have l5 : τ * ε ≤ b / 4 * T + α / 2 * A := by
    have h1 := mul_le_mul_of_nonneg_left hann hτ0.le
    have h2 := mul_le_mul_of_nonneg_right hτb hT0
    have h3 := mul_le_mul_of_nonneg_right hτκ hA0
    linarith
  have hXR : R - 75 * ε ≤ X := by
    have hε2 : ε * ε ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 hε0
    linarith
  have l6 : c * X ≤ X := by
    have := mul_le_mul_of_nonneg_right hc1 hX0
    linarith
  have l7 : c * R - 75 * c * ε ≤ c * X := by
    have := mul_le_mul_of_nonneg_left hXR hc0.le
    linarith
  have l8 : 75 * c * ε ≤ b / 8 * T + α / 4 * A := by
    have h1 := mul_le_mul_of_nonneg_left hann (by positivity : (0 : ℝ) ≤ 75 * c)
    have h2 : 75 * c * T ≤ b / 8 * T := mul_le_mul_of_nonneg_right (by linarith) hT0
    have h3 : 75 * c * κ * A ≤ α / 4 * A := by
      have h5 : 75 * c * κ ≤ α / 4 := by
        have := mul_le_mul_of_nonneg_right hcτ hκ0.le
        linarith
      exact mul_le_mul_of_nonneg_right h5 hA0
    linarith
  have l9 : Cμ * P40 * L ^ 3 ≤ c / 2 * R := by
    have e : L ^ 3 = L * R := by rw [← hLR]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hsm3 hR0
    linarith
  have l10 : mabs * (N * Δ ^ 2 + P40 * L ^ 3) ≤ Cμ * (N * Δ ^ 2 + P40 * L ^ 3) :=
    mul_le_mul_of_nonneg_right hμ (by positivity)
  have l11 : Ci * A ≤ α / 4 * A := mul_le_mul_of_nonneg_right hCα hA0
  have l12 : Ci * T ≤ b / 8 * T := mul_le_mul_of_nonneg_right hCb hT0
  have l13 : Ci * R ≤ c / 2 * R := mul_le_mul_of_nonneg_right hCc hR0
  have hαA : α * A = a2 * A - θ * A := by rw [hα]; ring
  linarith only [hsplit, hent, hlaw, hc, hr, hk, hlag, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10,
    l11, l12, l13, hαA]

set_option maxHeartbeats 1000000 in
/-- **`lem:graphon-lagrangian-bound` for every decomposition close to the constant.**  There are
`ρ₀ > 0` and `ρ ↦ C_{d,ρ} ≥ 1` on `(0, ρ₀)` such that for every `d`-regular graph `H` with
`m ≥ 1` edges there is `C_{d,m} ≥ 1` with: for every `0 < ρ < ρ₀` and `K₀ ≥ 0` there is
`0 < h_ρ ≤ h₀` such that for all `0 < h < h_ρ`, every graphon `W` and every decomposition
`W = f ⊗ f + E` with `‖f - u_*‖₄ ≤ K₀h` and `‖E‖₂ ≤ K₀h`, and `ν` the law of `f`,

`I_{p_h}(W) - I_{p_h}(W_h) - μ_h{t(H,W) - r_h^m}
  ≥ C_{d,ρ}⁻¹[A_{h,ρ}(ν) + ν(𝒯_ρ) + ‖E‖₂²] - C_{d,m} Δ_h(ν)²`.

`C_{d,ρ} = max{1, 4/α, 8/b_ρ, 2/c_ρ}` with `α = d³/48 - θ`, `θ = min(1, d³/192)`,
`τ_ρ = min(b_ρ/4, α/(2(4/ρ)⁴))` and `c_ρ = min(1, τ_ρ/150)`; `C_{d,m} = C + C_μ v²(2^d)^{2v}`
with `C` the graph-free constant of `auxiliary_gap_bound_law` and `C_μ` a bound for `|μ_h|`. -/
theorem graphon_lagrangian_bound_of_close (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ Cρ : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → 1 ≤ Cρ ρ) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ v, H.degree v = d) → 1 ≤ H.edgeFinset.card →
        ∃ Cm : ℝ, 1 ≤ Cm ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∀ K₀ : ℝ, 0 ≤ K₀ →
          ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧
            ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < hρ →
            ∀ (W : Graphon) (P : FactorDecomp d W),
              Lnorm unitμ 4 (fun x => P.f x - uStar d) ≤ K₀ * h →
              P.residNorm ≤ K₀ * h →
              (Cρ ρ)⁻¹
                    * ((∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂(comparisonDistribution P.f))
                      + (comparisonDistribution P.f
                          (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
                      + P.residNorm ^ 2)
                  - Cm * ((∫ x, x ^ d ∂(comparisonDistribution P.f)) - B.qVal h) ^ 2
                ≤ W.Ip (B.p h) - (B.graphon hh).Ip (B.p h)
                    - B.muVal (H.edgeFinset.card : ℝ) h
                      * (W.tDensity H - B.rVal h ^ H.edgeFinset.card) := by
  classical
  have hd3 : (0 : ℝ) < (d : ℝ) ^ 3 := pow_pos (dpos hd) 3
  -- the KKT smallness of the central square
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = min 1 ((d : ℝ) ^ 3 / 192) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; exact lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := by rw [hθdef]; exact min_le_left _ _
  have hθd : θ ≤ (d : ℝ) ^ 3 / 192 := by rw [hθdef]; exact min_le_right _ _
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = (d : ℝ) ^ 3 / 24 / 2 - θ := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; linarith only [hθd, hd3]
  obtain ⟨ρC, hρC0, -, -, hcentall⟩ := comparisonMain_exists_central_bound hd B hθ0
  obtain ⟨ρL, C₁, hρL0, hC₁, hlaw⟩ := auxiliary_gap_bound_law hd B
  choose! b hb0 hlawb using hlaw
  obtain ⟨cf, hcf⟩ : ∃ cf : ℝ → ℝ,
      ∀ ρ, cf ρ = min 1 (min (b ρ / 4) (α / (2 * (4 / ρ) ^ 4)) / 150) := ⟨_, fun _ => rfl⟩
  obtain ⟨Cρ, hCρ⟩ : ∃ Cρ : ℝ → ℝ,
      ∀ ρ, Cρ ρ = max (max 1 (4 / α)) (max (8 / b ρ) (2 / cf ρ)) := ⟨_, fun _ => rfl⟩
  refine ⟨min ρL ρC, lt_min hρL0 hρC0, Cρ,
    fun ρ _ _ => by rw [hCρ ρ]; exact le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro V _ _ H _ hreg hcard
  -- the graph enters through `μ_h` and the rank-one splitting of `t(H,W)`
  have hv := graphonLagrangian_two_le_card H hd hreg hcard
  have hmpos : (0 : ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hcard
  obtain ⟨Cμ, δμ, hCμ, hδμ, hμbd⟩ := B.exists_abs_muVal_le hmpos
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ,
      N = (Fintype.card V : ℝ) ^ 2 * (2 ^ d : ℝ) ^ (2 * Fintype.card V) := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  refine ⟨C₁ + Cμ * N, by linarith only [hC₁, mul_nonneg hCμ.le hN0], ?_⟩
  intro ρ hρ0 hρlt K₀ hK₀
  have hρL : ρ < ρL := lt_of_lt_of_le hρlt (min_le_left _ _)
  have hρ2 : 0 < ρ / 2 := half_pos hρ0
  have hρC : ρ / 2 ≤ ρC := by linarith only [lt_of_lt_of_le hρlt (min_le_right _ _), hρ0]
  have hbρ : 0 < b ρ := hb0 ρ hρ0 hρL
  -- the constants at this radius
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (4 / ρ) ^ 4 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; exact pow_pos (div_pos (by norm_num) hρ0) 4
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = min (b ρ / 4) (α / (2 * κ)) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτdef]; exact lt_min (by positivity) (by positivity)
  have hτb : τ ≤ b ρ / 4 := by rw [hτdef]; exact min_le_left _ _
  have hτκ : τ * κ ≤ α / 2 := by
    have h1 : τ ≤ α / (2 * κ) := by rw [hτdef]; exact min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 hκ0.le
    have h3 : α / (2 * κ) * κ = α / 2 := by field_simp
    linarith only [h2, h3]
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = cf ρ := ⟨_, rfl⟩
  have hc' : c = min 1 (τ / 150) := by rw [hcdef, hcf ρ, hτdef, hκdef]
  have hc0 : 0 < c := by rw [hc']; exact lt_min one_pos (by positivity)
  have hc1 : c ≤ 1 := by rw [hc']; exact min_le_left _ _
  have hcτ : c ≤ τ / 150 := by rw [hc']; exact min_le_right _ _
  have hCinvα : (Cρ ρ)⁻¹ ≤ α / 4 := by
    have h1 : 4 / α ≤ Cρ ρ := by
      rw [hCρ ρ]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    calc (Cρ ρ)⁻¹ ≤ (4 / α)⁻¹ := inv_anti₀ (by positivity) h1
      _ = α / 4 := inv_div 4 α
  have hCinvb : (Cρ ρ)⁻¹ ≤ b ρ / 8 := by
    have h1 : 8 / b ρ ≤ Cρ ρ := by
      rw [hCρ ρ]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    calc (Cρ ρ)⁻¹ ≤ (8 / b ρ)⁻¹ := inv_anti₀ (by positivity) h1
      _ = b ρ / 8 := inv_div 8 (b ρ)
  have hCinvc : (Cρ ρ)⁻¹ ≤ c / 2 := by
    have h1 : 2 / c ≤ Cρ ρ := by
      rw [hCρ ρ, ← hcdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    calc (Cρ ρ)⁻¹ ≤ (2 / c)⁻¹ := inv_anti₀ (by positivity) h1
      _ = c / 2 := inv_div 2 c
  -- the residual half at the closed radius `ρ/2`
  obtain ⟨CC, hCC, δC, hδC, hcent⟩ := hcentall (ρ / 2) hρ2 hρC
  obtain ⟨CK, hCK, δK, hδK, hcorner⟩ := rowJensen_exists_tailSq hd B (ρ / 2)
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = K₀ ^ 4 + 16 * K₀ ^ 4 / ρ ^ 4 := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK'def]; positivity
  obtain ⟨δR, hδR, hmix⟩ :=
    rowJensen_exists_mixed hd B (ρ / 2) (β := τ / 3) (by positivity) hK'0
  -- the law half at the open radius `ρ`
  obtain ⟨hL, hL0, hLle, hlawK⟩ :=
    hlawb ρ hρ0 hρL ((9 + 8 * K₀ ^ 4) + K₀ ^ 4 / ρ ^ 4) (by positivity)
  obtain ⟨δu, hδu, hu⟩ := exists_abs_u_sub_le B
  -- the smallness of `h`
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = min 1 (min ((τ / 3) / (CC * K₀ + 1))
      (min ((τ / 3) / (CK * K' + 1)) ((c / 2) / (Cμ * 40 ^ H.edgeFinset.card * K₀ + 1)))) :=
    ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hsdef]
    exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  refine ⟨min hL (min δu (min δC (min δR (min δK (min δμ (min (ρ / 8) s)))))),
    lt_min hL0 (lt_min hδu (lt_min hδC (lt_min hδR (lt_min hδK (lt_min hδμ
      (lt_min (by positivity) hs0)))))),
    le_trans (min_le_left _ _) hLle, ?_⟩
  intro h hh hpos hlt W P hclose hres
  have hlt1 := lt_of_lt_of_le hlt (min_le_right _ _)
  have hlt2 := lt_of_lt_of_le hlt1 (min_le_right _ _)
  have hlt3 := lt_of_lt_of_le hlt2 (min_le_right _ _)
  have hlt4 := lt_of_lt_of_le hlt3 (min_le_right _ _)
  have hlt5 := lt_of_lt_of_le hlt4 (min_le_right _ _)
  have hlt6 := lt_of_lt_of_le hlt5 (min_le_right _ _)
  have hhL : h < hL := lt_of_lt_of_le hlt (min_le_left _ _)
  have hhu : h < δu := lt_of_lt_of_le hlt1 (min_le_left _ _)
  have hhC : h < δC := lt_of_lt_of_le hlt2 (min_le_left _ _)
  have hhR : h < δR := lt_of_lt_of_le hlt3 (min_le_left _ _)
  have hhK : |h| < δK := by rw [abs_of_pos hpos]; exact lt_of_lt_of_le hlt4 (min_le_left _ _)
  have hhμ : |h| < δμ := by rw [abs_of_pos hpos]; exact lt_of_lt_of_le hlt5 (min_le_left _ _)
  have hhρ : h ≤ ρ / 8 := (lt_of_lt_of_le hlt6 (min_le_left _ _)).le
  have hhs : h ≤ s := (lt_of_lt_of_le hlt6 (min_le_right _ _)).le
  have hh1 : h ≤ 1 := le_trans hhs (by rw [hsdef]; exact min_le_left _ _)
  have hhs1 : h ≤ (τ / 3) / (CC * K₀ + 1) :=
    le_trans hhs (by rw [hsdef]; exact le_trans (min_le_right _ _) (min_le_left _ _))
  have hhs2 : h ≤ (τ / 3) / (CK * K' + 1) := le_trans hhs (by
    rw [hsdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hhs3 : h ≤ (c / 2) / (Cμ * 40 ^ H.edgeFinset.card * K₀ + 1) := le_trans hhs (by
    rw [hsdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have huh := hu h hpos hhu
  have hf := P.meas_f
  have hnn := P.f_nonneg
  have hbd := P.f_bdd
  -- the a-priori bounds
  have h4 : (∫ x, (P.f x - uStar d) ^ 4 ∂unitμ) ≤ (K₀ * h) ^ 4 :=
    integral_pow_four_le_of_Lnorm hclose
  have hh4 : (0 : ℝ) ≤ h ^ 4 := by positivity
  have hquart' : (∫ x, (P.f x - uStar d) ^ 4 ∂unitμ) ≤ K' * h ^ 4 := by
    refine le_trans h4 (le_of_eq_of_le (mul_pow K₀ h 4) (mul_le_mul_of_nonneg_right ?_ hh4))
    rw [hK'def]
    linarith only [show (0 : ℝ) ≤ 16 * K₀ ^ 4 / ρ ^ 4 by positivity]
  have hbdabs : ∀ x, |P.f x| ≤ 2 := fun x => abs_le.mpr ⟨by linarith only [hnn x], hbd x⟩
  have htailC : tailMass d (ρ / 2) P.f ≤ K' * h ^ 4 := by
    have h1 : (unitμ {x | P.f x ∉ centralWindow d (ρ / 2)}).toReal
        ≤ (K₀ * h) ^ 4 / (ρ / 2) ^ 4 :=
      factorTail_mass_le hf hbdabs hρ2 h4
    have hρne : ρ ≠ 0 := hρ0.ne'
    have h2 : (K₀ * h) ^ 4 / (ρ / 2) ^ 4 = 16 * K₀ ^ 4 / ρ ^ 4 * h ^ 4 := by
      field_simp
      ring
    have h3 : 16 * K₀ ^ 4 / ρ ^ 4 * h ^ 4 ≤ K' * h ^ 4 := by
      refine mul_le_mul_of_nonneg_right ?_ hh4
      rw [hK'def]
      linarith only [pow_nonneg hK₀ 4]
    show (unitμ {x | P.f x ∉ centralWindow d (ρ / 2)}).toReal ≤ K' * h ^ 4
    linarith only [h1, h2, h3]
  obtain ⟨hIν, hTν⟩ := law_apriori_le hf hnn hbd hpos hρ0 hclose huh
  have hlaw' := hlawK h hpos hhL _ (comparison_isProbabilityMeasure hf)
    (comparison_distribution_compl_Icc hf hnn hbd) hIν hTν
  -- the law quantities in the coordinate of the graphon
  have eA : (∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂(comparisonDistribution P.f))
      = ∫ x in {x | P.f x ∈ openWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ :=
    comparison_setIntegral hf (measurable_Qh_sq B h) (measurableSet_openWindow d ρ)
  have eT : (comparisonDistribution P.f (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
      = (unitμ {x | P.f x ∉ openWindow d ρ}).toReal := by
    rw [comparison_distribution_diff hf hnn hbd (measurableSet_openWindow d ρ)]
  have eq : (∫ x, x ^ d ∂(comparisonDistribution P.f)) = P.qVal :=
    comparison_distribution_moment hf d
  have eN : P.residNorm = P.residL2 := rfl
  rw [eA, eT, eq] at hlaw'
  rw [eA, eT, eq, eN, P.residL2_sq]
  -- the pieces
  have hsplit := comparison_splitting hd B hh W hf hnn hbd
  have hent := comparisonMain_entropy_split hd B hh P (ρ / 2)
  have hresid := comparisonMain_residSq_split P (ρ / 2)
  have hcor25 := comparisonMain_tailSq_resid_le P (ρ / 2)
  have hmixres := mixed_resid_le (ρ := ρ / 2) P
  have hc := hcent h hpos hhC hh W P
  have hr := hmix h hpos hhR hh W P htailC hquart'
  have hk := hcorner h hhK W P
  have hlag := muVal_tDensity_le_etaVal hd H hreg hv hcard B hh P
  rw [← hNdef] at hlag
  have hμ := hμbd h hhμ
  have hann := tailMass_half_le hf hnn hbd B hρ0 hpos.le hhρ huh
  rw [← hκdef] at hann
  have hA'A := setIntegral_centralSet_half_le hf hnn hbd B h hρ0
  have hset : centralSet d (ρ / 2) P.f = {x | P.f x ∈ centralWindow d (ρ / 2)} := rfl
  have hsetc : (centralSet d (ρ / 2) P.f)ᶜ = {x | P.f x ∉ centralWindow d (ρ / 2)} := rfl
  have hepsdef : (unitμ (centralSet d (ρ / 2) P.f)ᶜ).toReal = tailMass d (ρ / 2) P.f := rfl
  simp only [← hset, ← hsetc, hepsdef] at hc hent hresid hcor25
  -- nonnegativity and the small error coefficients
  have hA0 : 0 ≤ ∫ x in {x | P.f x ∈ openWindow d ρ}, B.Qh h (P.f x) ^ 2 ∂unitμ :=
    setIntegral_nonneg (hf (measurableSet_openWindow d ρ)) fun x _ => sq_nonneg _
  have hT0 : 0 ≤ (unitμ {x | P.f x ∉ openWindow d ρ}).toReal := ENNReal.toReal_nonneg
  have hε0 : 0 ≤ tailMass d (ρ / 2) P.f := tailMass_nonneg d (ρ / 2) P.f
  have hε1 : tailMass d (ρ / 2) P.f ≤ 1 := by
    rw [tailMass]
    exact measureReal_le_one
  have hX0 : 0 ≤ ∫ z : ℝ × ℝ, comparisonMainChi d (ρ / 2) P.f z.1
      * comparisonMainChi d (ρ / 2) P.f z.2 * P.resid z.1 z.2 ^ 2 ∂gμ :=
    integral_nonneg fun z => by
      have h1 := comparisonMainChi_nonneg d (ρ / 2) P.f z.1
      have h2 := comparisonMainChi_nonneg d (ρ / 2) P.f z.2
      positivity
  have hLK : P.residL2 ≤ K₀ * h := by rw [← eN]; exact hres
  have hsm1 : CC * P.residL2 ≤ τ / 3 :=
    calc CC * P.residL2 ≤ CC * (K₀ * h) := mul_le_mul_of_nonneg_left hLK hCC.le
      _ = CC * K₀ * h := by ring
      _ ≤ τ / 3 := graphonLagrangian_mul_le (by positivity) hpos.le hhs1
  have hsm2 : CK * tailMass d (ρ / 2) P.f ≤ τ / 3 :=
    calc CK * tailMass d (ρ / 2) P.f ≤ CK * (K' * h) := by
          refine mul_le_mul_of_nonneg_left (le_trans htailC ?_) hCK.le
          exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hpos.le hh1 (by norm_num)) hK'0
      _ = CK * K' * h := by ring
      _ ≤ τ / 3 := graphonLagrangian_mul_le (by positivity) hpos.le hhs2
  have hsm3 : Cμ * 40 ^ H.edgeFinset.card * P.residL2 ≤ c / 2 :=
    calc Cμ * 40 ^ H.edgeFinset.card * P.residL2
        ≤ Cμ * 40 ^ H.edgeFinset.card * (K₀ * h) :=
          mul_le_mul_of_nonneg_left hLK (by positivity)
      _ = Cμ * 40 ^ H.edgeFinset.card * K₀ * h := by ring
      _ ≤ c / 2 := graphonLagrangian_mul_le (by positivity) hpos.le hhs3
  exact graphonLagrangian_algebra hsplit hent hlaw' hc hr hk hlag hμ hresid hmixres hcor25 hann
    hA'A hA0 hT0 hε0 hε1 hX0 P.residL2_nonneg P.residSq_nonneg P.residL2_sq hN0 (by positivity)
    hθ0 hθ1 hαdef hτ0 hτb hτκ hκ0 hc0 hc1 hcτ hsm1 hsm2 hsm3 hCinvα hCinvb hCinvc

/-- **`lem:graphon-lagrangian-bound`.**  Let `C_d` be the constant of
`lem:localization-rank-one`.  There are `ρ₀ > 0` and `ρ ↦ C_{d,ρ} ≥ 1` on `(0, ρ₀)` such that
for every `d`-regular graph `H` with `m ≥ 1` edges there is `C_{d,m} ≥ 1` with: for every
`0 < ρ < ρ₀` there is `0 < h_ρ ≤ h₀` such that for all `0 < h < h_ρ` and every graphon `W` with
`t(H,W) ≥ r_h^m` and `I_{p_h}(W) ≤ I_{p_h}(W_h)`, the decomposition `W = f ⊗ f + E` of
`lem:localization-rank-one` (with all its properties) satisfies, for `ν` the law of `f`,

`[I_{p_h}(W) - μ_h{t(H,W) - r_h^m}] - [I_{p_h}(W_h) - μ_h{t(H,W_h) - r_h^m}]
  = I_{p_h}(W) - I_{p_h}(W_h) - μ_h{t(H,W) - r_h^m}
  ≥ C_{d,ρ}⁻¹[A_{h,ρ}(ν) + ν(𝒯_ρ) + ‖E‖₂²] - C_{d,m} Δ_h(ν)²`. -/
theorem graphon_lagrangian_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C₀ : ℝ, 1 < C₀ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ Cρ : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → 1 ≤ Cρ ρ) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ v, H.degree v = d) → 1 ≤ H.edgeFinset.card →
        ∃ Cm : ℝ, 1 ≤ Cm ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
          ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧
            ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < hρ →
            ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
              W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
              ∃ P : FactorDecomp d W,
                ((∀ x y, W.toFun x y = P.f x * P.f y + P.resid x y) ∧
                  MemLp P.f d unitμ ∧ MemLp (fun z : ℝ × ℝ => P.resid z.1 z.2) 2 gμ ∧
                  (∀ᵐ x ∂unitμ, kernelOp W.toFun (fun y => P.f y ^ (d - 1)) x = P.qVal * P.f x) ∧
                  (∀ᵐ x ∂unitμ, kernelOp P.resid (fun y => P.f y ^ (d - 1)) x = 0) ∧
                  0 < P.qVal ∧ (∀ x, 0 ≤ P.f x ∧ P.f x ≤ 2) ∧
                  Lnorm unitμ 4 (fun x => P.f x - uStar d) ≤ C₀ * h ∧
                  P.residNorm ≤ C₀ * h ∧
                  |P.qVal - B.qVal h| ≤ C₀ * h ^ 2 ∧
                  |W.tDensity H - P.qVal ^ Fintype.card V|
                    ≤ (40 : ℝ) ^ H.edgeFinset.card * P.residNorm ^ 3) ∧
                (W.Ip (B.p h) - B.muVal (H.edgeFinset.card : ℝ) h
                      * (W.tDensity H - B.rVal h ^ H.edgeFinset.card))
                    - ((B.graphon hh).Ip (B.p h) - B.muVal (H.edgeFinset.card : ℝ) h
                      * ((B.graphon hh).tDensity H - B.rVal h ^ H.edgeFinset.card))
                  = W.Ip (B.p h) - (B.graphon hh).Ip (B.p h)
                    - B.muVal (H.edgeFinset.card : ℝ) h
                      * (W.tDensity H - B.rVal h ^ H.edgeFinset.card) ∧
                (Cρ ρ)⁻¹
                      * ((∫ x in openWindow d ρ, B.Qh h x ^ 2 ∂(comparisonDistribution P.f))
                        + (comparisonDistribution P.f
                            (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
                        + P.residNorm ^ 2)
                    - Cm * ((∫ x, x ^ d ∂(comparisonDistribution P.f)) - B.qVal h) ^ 2
                  ≤ W.Ip (B.p h) - (B.graphon hh).Ip (B.p h)
                    - B.muVal (H.edgeFinset.card : ℝ) h
                      * (W.tDensity H - B.rVal h ^ H.edgeFinset.card) := by
  obtain ⟨C₀, hC₀, h₀, hh₀, -, hloc⟩ := localization_rank_one_reduction hd B
  obtain ⟨ρ₀, hρ₀, Cρ, hCρ1, hgen⟩ := graphon_lagrangian_bound_of_close hd B
  refine ⟨C₀, hC₀, ρ₀, hρ₀, Cρ, hCρ1, ?_⟩
  intro V _ _ H _ hreg hcard
  obtain ⟨Cm, hCm1, hgenH⟩ := hgen H hreg hcard
  refine ⟨Cm, hCm1, fun ρ hρ0 hρlt => ?_⟩
  obtain ⟨hρ, hρ0', hρle, hbound⟩ := hgenH ρ hρ0 hρlt C₀ (by linarith)
  refine ⟨min hρ h₀, lt_min hρ0' hh₀, le_trans (min_le_left _ _) hρle, ?_⟩
  intro h hh hpos hlt W hfeas hcost
  obtain ⟨-, P, hP⟩ :=
    hloc H hreg hcard h hh hpos (lt_of_lt_of_le hlt (min_le_right _ _)) W hfeas hcost
  refine ⟨P, hP, ?_, hbound h hh hpos (lt_of_lt_of_le hlt (min_le_left _ _)) W P
    hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1⟩
  rw [KKTFamily.graphon_tDensity_eq_rVal_pow H hd hreg hh]
  ring

end SingularEndpoint

end UpperTailOptimizers
