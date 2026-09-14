import UpperTailOptimizers.SingularEndpoint.GraphonComparison.GraphonLagrangianBound

/-!
# Paper forms of `eq:factor-tail-mass` and of the two Lagrangian bounds of Section 5

## `eq:factor-tail-mass`

`paper/sections/singular_auxiliary_lagrangian.tex` states, for the decomposition
`W = f ⊗ f + E` furnished by `lem:localization-rank-one` and `ν` the distribution of the values
of `f`: for every fixed `ρ > 0` there is `C_{d,ρ} ≥ 1` with

`ν(𝒯_ρ) ≤ ρ⁻⁴‖f - u_*‖₄⁴ ≤ C_{d,ρ}h⁴`,   `𝒯_ρ = [0,2] ∖ (u_* - ρ, u_* + ρ)`.

* `factor_tail_mass_le_Lnorm` — the Chebyshev inequality `ν(𝒯_ρ) ≤ ρ⁻⁴‖f - u_*‖₄⁴` for every
  measurable `f` valued in `[0,2]`;
* `factor_tail_mass_of_close` — both inequalities, with `C = K₀⁴/ρ⁴`, when `‖f - u_*‖₄ ≤ K₀h`;
* `factor_tail_mass` — the paper form: the conclusion of `localization_rank_one_reduction`
  (with the same constants `C_d`, `h₀`), and for the decomposition `P` it produces, both
  inequalities for **every** `ρ > 0`, with `C_{d,ρ} = max(1, C_d⁴/ρ⁴)`.  `C_{d,ρ}` is chosen before
  the graph, `h` and `W`, and the decomposition does not depend on `ρ`.

The only properties of the decomposition used are `‖f - u_*‖₄ ≤ C_d h` and `0 ≤ f ≤ 2`, both
provided by `localization_rank_one_reduction`; neither the pointwise Factor equation nor
`q(f) ≥ 2^{-d}` (hypotheses of the graph-dependent `family_factor_tail_mass`) is needed.

## `lem:auxiliary-lagrangian-bound` and `lem:graphon-lagrangian-bound`

Both lemmas fix the graph `H` (with `m` edges and `v = 2m/d` vertices) and assert constants
`C_{d,m}`.  `auxiliary_lagrangian_bound` and `graphon_lagrangian_bound` choose `C_{d,m}` after
`H`; the two theorems below choose it after `m` only, and in fact also choose `h_ρ` before `H`:

* `auxiliary_lagrangian_bound_uniform` — from `auxiliary_lagrangian_bound_of_close`, whose
  constant already depends on `(n, m)` only;
* `graphon_lagrangian_bound_uniform` — from `graphon_lagrangian_bound_of_close_uniform`.

The rest of each conclusion (the decomposition of `lem:localization-rank-one` with all its
properties, the displayed identity and the inequality) is verbatim that of the graph-dependent
form.
-/

universe u

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## `eq:factor-tail-mass` -/

/-- **`eq:factor-tail-mass`, the Chebyshev step.**  For every measurable `f` valued in `[0,2]`,
`ν` the law of `f` and `ρ > 0`: `ν(𝒯_ρ) ≤ ρ⁻⁴‖f - u_*‖₄⁴`, `𝒯_ρ = [0,2] ∖ (u_* - ρ, u_* + ρ)`. -/
theorem factor_tail_mass_le_Lnorm {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) {ρ : ℝ} (hρ : 0 < ρ) :
    (comparisonDistribution f (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
      ≤ (ρ ^ 4)⁻¹ * Lnorm unitμ 4 (fun x => f x - uStar d) ^ 4 := by
  have h := tail_openWindow_le (d := d) hf hnn hbd hρ
    (le_of_eq (factorTail_Lnorm_four_pow unitμ fun x => f x - uStar d).symm)
  rwa [div_eq_inv_mul] at h

/-- **`eq:factor-tail-mass` for a factor close to `u_*`.**  If `f` is measurable, valued in
`[0,2]`, and `‖f - u_*‖₄ ≤ K₀h`, then for every `ρ > 0` and `ν` the law of `f`,

`ν(𝒯_ρ) ≤ ρ⁻⁴‖f - u_*‖₄⁴ ≤ (K₀⁴/ρ⁴)h⁴`. -/
theorem factor_tail_mass_of_close {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hbd : ∀ x, f x ≤ 2) {ρ K₀ h : ℝ} (hρ : 0 < ρ)
    (hL : Lnorm unitμ 4 (fun x => f x - uStar d) ≤ K₀ * h) :
    (comparisonDistribution f (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
        ≤ (ρ ^ 4)⁻¹ * Lnorm unitμ 4 (fun x => f x - uStar d) ^ 4 ∧
      (ρ ^ 4)⁻¹ * Lnorm unitμ 4 (fun x => f x - uStar d) ^ 4 ≤ K₀ ^ 4 / ρ ^ 4 * h ^ 4 := by
  refine ⟨factor_tail_mass_le_Lnorm hf hnn hbd hρ, ?_⟩
  have h4 : Lnorm unitμ 4 (fun x => f x - uStar d) ^ 4 ≤ (K₀ * h) ^ 4 :=
    pow_le_pow_left₀ (Lnorm_nonneg _ _ _) hL 4
  calc (ρ ^ 4)⁻¹ * Lnorm unitμ 4 (fun x => f x - uStar d) ^ 4 ≤ (ρ ^ 4)⁻¹ * (K₀ * h) ^ 4 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = K₀ ^ 4 / ρ ^ 4 * h ^ 4 := by ring

/-- **`eq:factor-tail-mass`.**  Let `C_d > 1` and `h₀` be the constants of
`lem:localization-rank-one`.  There is `ρ ↦ C_{d,ρ} ≥ 1` (namely `max(1, C_d⁴/ρ⁴)`) such that for
every finite `d`-regular graph `H` with at least one edge, every `0 < h < h₀` and every graphon
`W` with `t(H,W) ≥ r_h^m` and `I_{p_h}(W) ≤ I_{p_h}(W_h)`, the conclusion of
`lem:localization-rank-one` holds (verbatim as in `localization_rank_one_reduction`), and the
decomposition `W = f ⊗ f + E` furnished there satisfies, for every `ρ > 0` and `ν` the law of `f`,

`ν(𝒯_ρ) ≤ ρ⁻⁴‖f - u_*‖₄⁴ ≤ C_{d,ρ}h⁴`,   `𝒯_ρ = [0,2] ∖ (u_* - ρ, u_* + ρ)`.

`C_{d,ρ}` depends only on `d`, the family `B` and `ρ`: it is chosen before the graph. -/
theorem factor_tail_mass (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C : ℝ, 1 < C ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ B.h₀ ∧
      ∃ Cρ : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → 1 ≤ Cρ ρ) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ v, H.degree v = d) → 1 ≤ H.edgeFinset.card →
        ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < h₀ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          Lnorm gμ 4 (fun z : ℝ × ℝ => W.toFun z.1 z.2 - rStar d) ≤ C * h ∧
          ∃ P : FactorDecomp d W,
            ((∀ x y, W.toFun x y = P.f x * P.f y + P.resid x y) ∧
              MemLp P.f d unitμ ∧ MemLp (fun z : ℝ × ℝ => P.resid z.1 z.2) 2 gμ ∧
              (∀ᵐ x ∂unitμ, kernelOp W.toFun (fun y => P.f y ^ (d - 1)) x = P.qVal * P.f x) ∧
              (∀ᵐ x ∂unitμ, kernelOp P.resid (fun y => P.f y ^ (d - 1)) x = 0) ∧
              0 < P.qVal ∧ (∀ x, 0 ≤ P.f x ∧ P.f x ≤ 2) ∧
              Lnorm unitμ 4 (fun x => P.f x - uStar d) ≤ C * h ∧
              P.residNorm ≤ C * h ∧
              |P.qVal - B.qVal h| ≤ C * h ^ 2 ∧
              |W.tDensity H - P.qVal ^ Fintype.card V|
                ≤ (40 : ℝ) ^ H.edgeFinset.card * P.residNorm ^ 3) ∧
            ∀ ρ : ℝ, 0 < ρ →
              (comparisonDistribution P.f (Set.Icc (0 : ℝ) 2 \ openWindow d ρ)).toReal
                  ≤ (ρ ^ 4)⁻¹ * Lnorm unitμ 4 (fun x => P.f x - uStar d) ^ 4 ∧
                (ρ ^ 4)⁻¹ * Lnorm unitμ 4 (fun x => P.f x - uStar d) ^ 4 ≤ Cρ ρ * h ^ 4 := by
  obtain ⟨C, hC, h₀, hh₀, hh₀le, hloc⟩ := localization_rank_one_reduction hd B
  refine ⟨C, hC, h₀, hh₀, hh₀le, fun ρ => max 1 (C ^ 4 / ρ ^ 4), fun ρ _ => le_max_left _ _, ?_⟩
  intro V _ _ H _ hreg hcard h hh hpos hlt W hfeas hcost
  obtain ⟨hW, P, hP⟩ := hloc H hreg hcard h hh hpos hlt W hfeas hcost
  refine ⟨hW, P, hP, fun ρ hρ => ?_⟩
  obtain ⟨h1, h2⟩ := factor_tail_mass_of_close P.meas_f P.f_nonneg P.f_bdd hρ
    hP.2.2.2.2.2.2.2.1
  exact ⟨h1, le_trans h2 (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))⟩

/-! ## `lem:auxiliary-lagrangian-bound` with `C_{d,m}` chosen before the graph -/

/-- **`lem:auxiliary-lagrangian-bound`, with `C_{d,m}` chosen before the graph.**  Let `C_d` be
the constant of `lem:localization-rank-one`.  There are `ρ₀ > 0` and `ρ ↦ b_ρ > 0` on `(0, ρ₀)`
such that for every `m ≥ 1` there is `C_{d,m} ≥ 1` with: for every `0 < ρ < ρ₀` there is
`0 < h_ρ ≤ h₀` such that for every `d`-regular graph `H` with `m` edges and `v` vertices, all
`0 < h < h_ρ` and every graphon `W` with `t(H,W) ≥ r_h^m` and `I_{p_h}(W) ≤ I_{p_h}(W_h)`, the
decomposition `W = f ⊗ f + E` of `lem:localization-rank-one` (with all its properties)
satisfies, for `ν` the law of `f`,

`𝓛_h(ν) - 𝓛_h(ν_h) = 𝒥_h(ν) - 𝒥_h(ν_h) - μ_h{m_d(ν)^v - q_h^v}
  ≥ (a/2) A_{h,ρ}(ν) + (b_ρ/2) ν(𝒯_ρ) - C_{d,m} Δ_h(ν)²`,   `a = d³/24`.

The conclusion is verbatim that of `auxiliary_lagrangian_bound`; only the graph is quantified
after the constants. -/
theorem auxiliary_lagrangian_bound_uniform (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C₀ : ℝ, 1 < C₀ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ b : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → 0 < b ρ) ∧
      ∀ m : ℕ, 1 ≤ m →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
          ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧
            ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
            (∀ v, H.degree v = d) → H.edgeFinset.card = m →
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
  refine ⟨C₀, hC₀, ρ₀, hρ₀, b, hb0, fun m hm => ?_⟩
  by_cases hex : ∃ n : ℕ, 2 * m = n * d ∧ 2 ≤ n
  · obtain ⟨n, hmn, hn2⟩ := hex
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hnR : 2 * (m : ℝ) = (n : ℝ) * (d : ℝ) := by exact_mod_cast hmn
    obtain ⟨C, hC1, hgenC⟩ := hgen hmpos hnR hn2
    refine ⟨C, hC1, fun ρ hρ0 hρlt => ?_⟩
    obtain ⟨hρ, hρ0', hρle, hbound⟩ := hgenC ρ hρ0 hρlt C₀ (by linarith)
    refine ⟨min hρ h₀, lt_min hρ0' hh₀, le_trans (min_le_left _ _) hρle, ?_⟩
    intro V _ _ H _ hreg hcard h hh hpos hlt W hfeas hcost
    have hVn : Fintype.card V = n := by
      have h1 := factorMain_two_mul_card_edgeFinset H hreg
      rw [hcard, hmn] at h1
      exact (Nat.eq_of_mul_eq_mul_right (by omega) h1).symm
    obtain ⟨-, P, hP⟩ := hloc H hreg (by omega) h hh hpos
      (lt_of_lt_of_le hlt (min_le_right _ _)) W hfeas hcost
    refine ⟨P, hP, ?_, ?_⟩
    · rw [KKTFamily.auxLagrangian_distributionMeasure B hh, KKTFamily.auxLagrangian]
      ring
    · rw [hcard, hVn]
      exact hbound h hpos (lt_of_lt_of_le hlt (min_le_left _ _)) W P hP.2.2.2.2.2.2.2.1
  · -- no `d`-regular graph has `m` edges: the statement is vacuous
    refine ⟨1, le_rfl, fun ρ _ _ => ⟨B.h₀, B.h₀_pos, le_rfl, ?_⟩⟩
    intro V _ _ H _ hreg hcard
    refine absurd ⟨Fintype.card V, ?_, graphonLagrangian_two_le_card H hd hreg (by omega)⟩ hex
    rw [← hcard]
    exact factorMain_two_mul_card_edgeFinset H hreg

/-! ## `lem:graphon-lagrangian-bound` with `C_{d,m}` chosen before the graph -/

/-- **`lem:graphon-lagrangian-bound`, with `C_{d,m}` chosen before the graph.**  Let `C_d` be
the constant of `lem:localization-rank-one`.  There are `ρ₀ > 0` and `ρ ↦ C_{d,ρ} ≥ 1` on
`(0, ρ₀)` such that for every `m ≥ 1` there is `C_{d,m} ≥ 1` with: for every `0 < ρ < ρ₀` there
is `0 < h_ρ ≤ h₀` such that for every `d`-regular graph `H` with `m` edges, all `0 < h < h_ρ` and
every graphon `W` with `t(H,W) ≥ r_h^m` and `I_{p_h}(W) ≤ I_{p_h}(W_h)`, the decomposition
`W = f ⊗ f + E` of `lem:localization-rank-one` (with all its properties) satisfies, for `ν` the
law of `f`,

`[I_{p_h}(W) - μ_h{t(H,W) - r_h^m}] - [I_{p_h}(W_h) - μ_h{t(H,W_h) - r_h^m}]
  = I_{p_h}(W) - I_{p_h}(W_h) - μ_h{t(H,W) - r_h^m}
  ≥ C_{d,ρ}⁻¹[A_{h,ρ}(ν) + ν(𝒯_ρ) + ‖E‖₂²] - C_{d,m} Δ_h(ν)²`.

The conclusion is verbatim that of `graphon_lagrangian_bound`; only the graph is quantified
after the constants. -/
theorem graphon_lagrangian_bound_uniform (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C₀ : ℝ, 1 < C₀ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ Cρ : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → 1 ≤ Cρ ρ) ∧
      ∀ m : ℕ, 1 ≤ m →
        ∃ Cm : ℝ, 1 ≤ Cm ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
          ∃ hρ : ℝ, 0 < hρ ∧ hρ ≤ B.h₀ ∧
            ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
            (∀ v, H.degree v = d) → H.edgeFinset.card = m →
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
  obtain ⟨ρ₀, hρ₀, Cρ, hCρ1, hgen⟩ := graphon_lagrangian_bound_of_close_uniform hd B
  refine ⟨C₀, hC₀, ρ₀, hρ₀, Cρ, hCρ1, fun m hm => ?_⟩
  obtain ⟨Cm, hCm1, hgenm⟩ := hgen m hm
  refine ⟨Cm, hCm1, fun ρ hρ0 hρlt => ?_⟩
  obtain ⟨hρ, hρ0', hρle, hbound⟩ := hgenm ρ hρ0 hρlt C₀ (by linarith)
  refine ⟨min hρ h₀, lt_min hρ0' hh₀, le_trans (min_le_left _ _) hρle, ?_⟩
  intro V _ _ H _ hreg hcard h hh hpos hlt W hfeas hcost
  obtain ⟨-, P, hP⟩ := hloc H hreg (by omega) h hh hpos
    (lt_of_lt_of_le hlt (min_le_right _ _)) W hfeas hcost
  refine ⟨P, hP, ?_, hbound H hreg hcard h hh hpos (lt_of_lt_of_le hlt (min_le_left _ _)) W P
    hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1⟩
  rw [KKTFamily.graphon_tDensity_eq_rVal_pow H hd hreg hh]
  ring

end SingularEndpoint

end UpperTailOptimizers
