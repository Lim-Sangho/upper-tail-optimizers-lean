import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.LocalizationMain

/-!
# `lem:localization-rank-one` in the form of the paper

`lem:localization-rank-one` (`paper/sections/singular_localization.tex`) states: there are
`C_d, C_{d,m} > 1` and `h₀ > 0` such that for every `0 < h < h₀` and every graphon `W` with
`t(H,W) ≥ r_h^m` and `I_{p_h}(W) ≤ I_{p_h}(W_h)`,

* `‖W - r_*‖₄ ≤ C_d h`;
* `W = f ⊗ f + E` with `f ∈ L^d`, `E ∈ L²`, `T_W(f^{d-1}) = q(f) f`, `T_E(f^{d-1}) = 0`,
  `q(f) > 0` and `0 ≤ f ≤ 2` a.e.;
* `‖f - u_*‖₄ ≤ C_d h`, `‖E‖₂ ≤ C_d h`, `|q(f) - q_h| ≤ C_d h²` and
  `|t(H,W) - q(f)^v| ≤ C_{d,m} ‖E‖₂³`.

`localization_rank_one_reduction` states exactly this.  The subscripts are respected: `C` and
`h₀` are chosen **before** the graph `H` (they depend only on `d` and the family `B`), and
`C_{d,m}` is the explicit `40^m`.

The existing family-level localization lemmas quantify their constants after `H`, although `H`
enters their proofs only through the generalized Hölder consequence `r_h^d ≤ ∫W^d`.  The two
lemmas below restate them with that moment inequality as the hypothesis, which is what makes the
constants graph-independent:

* `gamInt_localized_of_moment` — `gamInt_localized` without `H`;
* `family_localization_of_moment` — the `L⁴` localization and the sharp moment bound
  `0 ≤ ∫W^d - r_h^d ≤ Mh⁴` along the family, without `H`.

The decomposition is `exists_factorDecomp`; the rates `‖E‖₂ ≤ Ch` and `|q - q_h| ≤ Ch²` come
from the closeness bound, `factorTail_residNorm_le_of_quart` and `factorTail_abs_qVal_sub_le`
(applied at `√h`), and the homomorphism-density bound is `abs_tDensity_sub_qVal_pow_le`.
`singular_endpoint_localization` (with its stronger rates and graph-dependent constant) is kept
unchanged for its consumer `exists_singular_endpoint_comparison_graph`.
-/

universe u

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-- **`gamInt_localized` with the moment inequality as hypothesis.**  Feasibility enters
`gamInt_localized` only through `holder_moment`, i.e. through `r^d ≤ ∫W^d`. -/
theorem gamInt_localized_of_moment (hd : 2 ≤ d) {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {W W' : Graphon} (hSS : r ^ d ≤ W.Wmoment d) (hmom : W'.Wmoment d = r ^ d)
    (hcost : W.Ip p ≤ W'.Ip p) {b0 Cc : ℝ} (hb0 : 0 < b0) (hCc : 0 < Cc)
    (hVG : ∀ X : Graphon, RdInt d X ^ 2 ≤ Cc * GamInt d X)
    (hb0le : b0 ≤ betaD d + (ell p - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1))) :
    b0 * (W.Wmoment d - r ^ d) + GamInt d W / 2
      ≤ GamInt d W' + |ell p - ell (pStar d)| * |RdInt d W'|
          + Cc * (ell p - ell (pStar d)) ^ 2 / 2 := by
  have hbasic := localization_basic hd hp0 hp1 hcost
  rw [hmom] at hbasic
  have hweak : b0 * (W.Wmoment d - r ^ d)
      ≤ (betaD d + (ell p - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1)))
          * (W.Wmoment d - r ^ d) :=
    mul_le_mul_of_nonneg_right hb0le (sub_nonneg.mpr hSS)
  have hmain : b0 * (W.Wmoment d - r ^ d) + GamInt d W
      ≤ GamInt d W' + (ell p - ell (pStar d)) * (RdInt d W - RdInt d W') := by
    linarith
  exact localization_absorption hb0 hSS (gamInt_nonneg hd W) (rdInt_nonneg hd W) hCc
    (hVG W) hmain

/-- **The `L⁴` localization and the sharp moment bound, with graph-independent constants.**
For `0 < h < δ` and every graphon `W` with `r_h^d ≤ ∫W^d` and `I_{p_h}(W) ≤ I_{p_h}(W_h)`,
`∫|W - r_*|⁴ ≤ Mh⁴` and `∫W^d - r_h^d ≤ Mh⁴`; `M` and `δ` depend only on `d` and `B`. -/
theorem family_localization_of_moment (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
        ∀ W : Graphon, B.rVal h ^ d ≤ W.Wmoment d →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          (∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ ≤ M * h ^ 4) ∧
            W.Wmoment d - B.rVal h ^ d ≤ M * h ^ 4 := by
  obtain ⟨Cc, hCc0, hVG, N, hN0, δ, hδ, hrhs⟩ := ldSharp_family_rhs hd B
  obtain ⟨c, hc0, hcG⟩ := integral_dist_pow_four_le_gamInt (d := d) hd
  have hbpos : 0 < betaD d := betaD_pos hd
  refine ⟨2 * N / c + 2 * N / betaD d, by positivity, δ, hδ, ?_⟩
  intro h hh hpos hlt W hSS hcost
  obtain ⟨hb4, hbnd⟩ := hrhs h hh hpos hlt
  have hkey := gamInt_localized_of_moment hd (B.p_mem h hh).1 (B.p_mem h hh).2 hSS
    (KKTFamily.graphon_Wmoment_eq_rVal_pow hd hh) hcost
    (show (0 : ℝ) < betaD d / 2 by linarith) hCc0 hVG hb4
  have hG : 0 ≤ GamInt d W := gamInt_nonneg hd W
  have hmnn : 0 ≤ W.Wmoment d - B.rVal h ^ d := sub_nonneg.mpr hSS
  have hc := hcG W
  have hprod : 0 ≤ betaD d / 2 * (W.Wmoment d - B.rVal h ^ d) :=
    mul_nonneg (by linarith) hmnn
  have hc4 : 0 ≤ 2 * N / c * h ^ 4 := by positivity
  have hb4' : 0 ≤ 2 * N / betaD d * h ^ 4 := by positivity
  constructor
  · have h1 : c * ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ ≤ 2 * N * h ^ 4 := by linarith
    have h2 : ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ ≤ 2 * N / c * h ^ 4 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
      linarith
    linarith
  · have h1 : betaD d / 2 * (W.Wmoment d - B.rVal h ^ d) ≤ N * h ^ 4 := by linarith
    have h2 : W.Wmoment d - B.rVal h ^ d ≤ 2 * N / betaD d * h ^ 4 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hbpos]
      linarith
    linarith

set_option maxHeartbeats 1000000 in
/-- **`lem:localization-rank-one`.**  There are `C > 1` and `0 < h₀ ≤ B.h₀`, depending only on
`d` and the family `B` — in particular chosen before the graph — such that for every finite
`d`-regular graph `H` with at least one edge, every `0 < h < h₀` and every graphon `W` with
`t(H,W) ≥ r_h^m` and `I_{p_h}(W) ≤ I_{p_h}(W_h)`:

* `‖W - r_*‖₄ ≤ Ch`;
* there is a decomposition `W = f ⊗ f + E` (a `FactorDecomp d W`) with `f ∈ L^d`, `E ∈ L²`,
  `T_W(f^{d-1}) = q(f) f` and `T_E(f^{d-1}) = 0` a.e., `q(f) > 0`, `0 ≤ f ≤ 2`, and
  `‖f - u_*‖₄ ≤ Ch`, `‖E‖₂ ≤ Ch`, `|q(f) - q_h| ≤ Ch²`,
  `|t(H,W) - q(f)^v| ≤ 40^m ‖E‖₂³`.

Here `‖·‖₄ = Lnorm _ 4`, `‖E‖₂ = residNorm`, `q(f) = qVal`, `T_K = kernelOp K`, `v = |V(H)|`,
`m = |E(H)|`, and `C_{d,m} = 40^m > 1`. -/
theorem localization_rank_one_reduction (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C : ℝ, 1 < C ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ B.h₀ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ v, H.degree v = d) → 1 ≤ H.edgeFinset.card →
        ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < h₀ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          Lnorm gμ 4 (fun z : ℝ × ℝ => W.toFun z.1 z.2 - rStar d) ≤ C * h ∧
          ∃ P : FactorDecomp d W,
            (∀ x y, W.toFun x y = P.f x * P.f y + P.resid x y) ∧
            MemLp P.f d unitμ ∧ MemLp (fun z : ℝ × ℝ => P.resid z.1 z.2) 2 gμ ∧
            (∀ᵐ x ∂unitμ, kernelOp W.toFun (fun y => P.f y ^ (d - 1)) x = P.qVal * P.f x) ∧
            (∀ᵐ x ∂unitμ, kernelOp P.resid (fun y => P.f y ^ (d - 1)) x = 0) ∧
            0 < P.qVal ∧ (∀ x, 0 ≤ P.f x ∧ P.f x ≤ 2) ∧
            Lnorm unitμ 4 (fun x => P.f x - uStar d) ≤ C * h ∧
            P.residNorm ≤ C * h ∧
            |P.qVal - B.qVal h| ≤ C * h ^ 2 ∧
            |W.tDensity H - P.qVal ^ Fintype.card V|
              ≤ (40 : ℝ) ^ H.edgeFinset.card * P.residNorm ^ 3 := by
  classical
  obtain ⟨M, hM0, δ, hδ, hloc⟩ := family_localization_of_moment hd B
  have hCS0 : 0 ≤ factorSolutionCloseConst d := factorMain_closeConst_nonneg hd
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.sqrt (Real.sqrt M) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Real.sqrt_nonneg _
  have hApow : A ^ 4 = M := by
    rw [hAdef, show Real.sqrt (Real.sqrt M) ^ 4 = (Real.sqrt (Real.sqrt M) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hM0.le]
  obtain ⟨CE, hCEdef⟩ : ∃ CE : ℝ, CE = factorSolutionCloseConst d * A := ⟨_, rfl⟩
  have hCE0 : 0 ≤ CE := by rw [hCEdef]; exact mul_nonneg hCS0 hA0
  have htail0 : 0 ≤ tailConst d := by unfold tailConst; positivity
  obtain ⟨Cq, hCqdef⟩ : ∃ Cq : ℝ, Cq = (M + tailConst d * CE ^ 2) / (1 / 2 ^ d) := ⟨_, rfl⟩
  have hCq0 : 0 < Cq := by rw [hCqdef]; positivity
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 1 + A + CE + Cq := ⟨_, rfl⟩
  have hC1 : 1 < C := by rw [hCdef]; linarith
  have hAC : A ≤ C := by rw [hCdef]; linarith
  have hCEC : CE ≤ C := by rw [hCdef]; linarith
  have hCqC : Cq ≤ C := by rw [hCdef]; linarith
  have hden : 0 < A + 1 := by linarith
  refine ⟨C, hC1, min (min δ 1) (min B.h₀ (factorEps2 d / (A + 1))),
    lt_min (lt_min hδ one_pos) (lt_min B.h₀_pos (div_pos (factorEps2_pos hd) hden)),
    le_trans (min_le_right _ _) (min_le_left _ _), ?_⟩
  intro V _ _ H _ hreg hm h hh hpos hlt W hfeas hcost
  have hltδ : h < δ := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle1 : h ≤ 1 := le_trans hlt.le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hltε : h < factorEps2 d / (A + 1) :=
    lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_right _ _))
  -- generalized Hölder: the only use of the graph in the localization
  have hSS : B.rVal h ^ d ≤ W.Wmoment d :=
    holder_moment H hreg hd W (KKTFamily.rVal_pos hd hh).le hm hfeas
  obtain ⟨hquart, hmom⟩ := hloc h hh hpos hltδ W hSS hcost
  -- `ε = ‖W - r_*‖₄ ≤ A h`
  have hcong : defectQuart d W = ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ := by
    unfold defectQuart
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun z => (Even.pow_abs (n := 4) (by norm_num) _).symm)
  have hdq : defectQuart d W ≤ M * h ^ 4 := by rw [hcong]; exact hquart
  have heps : contractionEps W d ≤ A * h := by
    refine factorTail_le_of_pow_four_le (contractionEps_nonneg W d) (by positivity) ?_
    rw [factorMain_contractionEps_pow_four, mul_pow, hApow]
    exact hdq
  have hepsε : contractionEps W d ≤ factorEps2 d := by
    have h1 : A * h ≤ A * (factorEps2 d / (A + 1)) := mul_le_mul_of_nonneg_left hltε.le hA0
    have h2 : A * (factorEps2 d / (A + 1)) ≤ factorEps2 d := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [factorEps2_pos hd]
    linarith
  -- the decomposition
  obtain ⟨P, hq0, hqlow, -, hclose⟩ := exists_factorDecomp hd W hepsε
  have hfnn : 0 ≤ Lnorm unitμ 4 (fun x => P.f x - uStar d) := Lnorm_nonneg _ _ _
  have hEnn : 0 ≤ Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2) := Lnorm_nonneg _ _ _
  have hCSeps : factorSolutionCloseConst d * contractionEps W d ≤ CE * h := by
    have h1 := mul_le_mul_of_nonneg_left heps hCS0
    rw [hCEdef]
    linarith [h1, show factorSolutionCloseConst d * (A * h) = factorSolutionCloseConst d * A * h by
      ring]
  have hf4 : Lnorm unitμ 4 (fun x => P.f x - uStar d) ≤ CE * h := by linarith
  have hE4 : Lnorm gμ 4 (fun z : ℝ × ℝ => P.resid z.1 z.2)
      ≤ factorSolutionCloseConst d * contractionEps W d := by linarith
  -- `‖E‖₂ ≤ CE h`
  have hRq : P.residQuart ≤ (CE * h) ^ 4 := by
    have h1 := factorMain_residQuart_le hE4
    calc P.residQuart ≤ factorSolutionCloseConst d ^ 4 * defectQuart d W := h1
      _ ≤ factorSolutionCloseConst d ^ 4 * (M * h ^ 4) :=
          mul_le_mul_of_nonneg_left hdq (by positivity)
      _ = (CE * h) ^ 4 := by rw [hCEdef, ← hApow]; ring
  have hres : P.residNorm ≤ CE * h := factorTail_residNorm_le_of_quart P hCE0 hpos.le hRq
  -- `|q - q_h| ≤ Cq h²`, from the `(h², h⁴)` estimate at `√h`
  have hqh0 : 0 ≤ B.qVal h := (KKTFamily.qVal_pos hh).le
  have hsq2 : Real.sqrt h ^ 2 = h := Real.sq_sqrt hpos.le
  have hsq4 : Real.sqrt h ^ 4 = h ^ 2 := by
    rw [show Real.sqrt h ^ 4 = (Real.sqrt h ^ 2) ^ 2 by ring, hsq2]
  have hh42 : h ^ 4 ≤ h ^ 2 := by
    have h2 : 0 ≤ h ^ 2 := sq_nonneg h
    have h3 : h ^ 2 ≤ 1 := pow_le_one₀ hpos.le hle1
    calc h ^ 4 = h ^ 2 * h ^ 2 := by ring
      _ ≤ h ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 h2
      _ = h ^ 2 := mul_one _
  have hmomq : |W.Wmoment d - B.qVal h ^ 2| ≤ M * Real.sqrt h ^ 4 := by
    rw [← KKTFamily.rVal_pow_d hd hh, hsq4, abs_of_nonneg (sub_nonneg.mpr hSS)]
    calc W.Wmoment d - B.rVal h ^ d ≤ M * h ^ 4 := hmom
      _ ≤ M * h ^ 2 := mul_le_mul_of_nonneg_left hh42 hM0.le
  have hresq : P.residNorm ≤ CE * Real.sqrt h ^ 2 := by rw [hsq2]; exact hres
  have hq := factorTail_abs_qVal_sub_le hd P (q₀ := 1 / 2 ^ d) (by positivity) hqlow hqh0
    hCE0 hmomq hresq
  rw [hsq4, ← hCqdef] at hq
  refine ⟨?_, P, fun x y => (P.rankOne_add_resid x y).symm, ?_, ?_, ?_, ?_, hq0,
    fun x => ⟨P.f_nonneg x, P.f_bdd x⟩, ?_, ?_, ?_, ?_⟩
  · -- `‖W - r_*‖₄ = ε ≤ A h ≤ C h`
    have h1 : contractionEps W d ≤ C * h :=
      le_trans heps (mul_le_mul_of_nonneg_right hAC hpos.le)
    exact h1
  · exact MemLp.of_bound P.meas_f.aestronglyMeasurable 2
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact P.abs_f_le x)
  · exact MemLp.of_bound P.measurable_resid.aestronglyMeasurable 5
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact P.abs_resid_le z.1 z.2)
  · filter_upwards [P.factor_eq (by omega : 1 ≤ d)] with x hx
    exact hx
  · filter_upwards [P.ortho] with x hx
    exact hx
  · exact le_trans hf4 (mul_le_mul_of_nonneg_right hCEC hpos.le)
  · exact le_trans hres (mul_le_mul_of_nonneg_right hCEC hpos.le)
  · exact le_trans hq (mul_le_mul_of_nonneg_right hCqC (sq_nonneg h))
  · exact P.abs_tDensity_sub_qVal_pow_le H hreg

end SingularEndpoint

end UpperTailOptimizers
