import UpperTailOptimizers.SingularEndpoint.Quartic
import UpperTailOptimizers.SingularEndpoint.Gap
import UpperTailOptimizers.SingularEndpoint.Identities

/-!
# The singular endpoint cost comparison (Section 7, `paper/singular_endpoint.tex`)

The graphon-level half of `sec:localization-rank-one`.  The section localizes a competitive
graphon by comparing costs at a parameter near the singular endpoint; the comparison itself,
`eq:graphon-cost-decomposition`, is an **exact identity**, and this file proves it, together
with the two integral estimates that make it usable:

* the edge/moment identity — the edge density is the `d`-th moment corrected by the Jensen
  defect `∫R_d(W)`;
* `Ip_sub_Ip_eq` / `localization_basic` — the cost comparison itself;
* `RdInt_sq_le_gamInt` — Cauchy–Schwarz against `R_d² ≤ C_dΓ_d`, the step the
  paper writes `𝒱_R² ≤ ∫R_d(W)² ≤ C_d 𝒢_Γ`;
* `integral_dist_pow_four_le_gamInt` — `eq:endpoint-gap-quartic-bound` integrated,
  i.e. `∫|W - r_*|⁴ ≤ c⁻¹ ∫Γ_d(W)`, which is what turns a bound on `𝒢_Γ` into
  `eq:graphon-quartic-localization`.

What is *not* here is the `O(h⁴)` input: bounding `𝒢_{Γ,h}`, `𝒱_{R,h}` and `Λ_h` along the
family needs the expansions `eq:rank-one-parameter-expansions`, and is done in
`SingularEndpoint/FamilyLocalization.lean` (`family_localization`) on top of the coercive step of
`SingularEndpoint/L4Bound.lean`.  The identities below are unconditional and hold for every graphon.

## Contents

* `RdInt` and `integrable_Rd`;
* `edge_eq_moment_sub_rdInt` — the edge/moment identity;
* `Ip_sub_Ip_eq`, `localization_basic` — `eq:graphon-cost-decomposition`;
* `RdInt_sq_le_gamInt`, `integral_dist_pow_four_le_gamInt`;
* `sq_integral_le_integral_sq` — Cauchy–Schwarz `(∫f)² ≤ ∫f²` on `gμ`, shared with
  `SingularEndpoint/FamilyLocalization.lean` and `SingularEndpoint/FactorTail.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Real

variable {d : ℕ}

/-! ## The Jensen defect integral -/

private theorem measurable_Rd (d : ℕ) : Measurable (Rd d) := by
  unfold Rd
  fun_prop

private theorem continuous_Rd (d : ℕ) : Continuous (Rd d) := by
  unfold Rd
  fun_prop

/-- The graphon integral `𝒱_R = ∫R_d(W)` of `sec:localization-rank-one`. -/
noncomputable def RdInt (d : ℕ) (W : Graphon) : ℝ :=
  ∫ z, Rd d (W.toFun z.1 z.2) ∂gμ

theorem integrable_Rd (d : ℕ) (W : Graphon) :
    Integrable (fun z : ℝ × ℝ => Rd d (W.toFun z.1 z.2)) gμ :=
  W.integrable_comp (measurable_Rd d) (continuous_Rd d).continuousOn

/-- **The edge/moment identity** at graphon level:
`e(W) - r_* = (∫W^d - r_*^d)/(d r_*^{d-1}) - ∫R_d(W)`. -/
theorem edge_eq_moment_sub_rdInt (hd : 2 ≤ d) (W : Graphon) :
    W.edgeDensity - rStar d
      = (W.Wmoment d - rStar d ^ d) / ((d : ℝ) * rStar d ^ (d - 1)) - RdInt d W := by
  have hIpow : Integrable (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d) gμ :=
    W.integrable_comp (continuous_pow d).measurable (continuous_pow d).continuousOn
  have hIrd : Integrable (fun z : ℝ × ℝ => Rd d (W.toFun z.1 z.2)) gμ := integrable_Rd d W
  have hIW : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2) gμ := W.integrable_self
  have hIscaled : Integrable
      (fun z : ℝ × ℝ => ((W.toFun z.1 z.2) ^ d - rStar d ^ d)
        * ((d : ℝ) * rStar d ^ (d - 1))⁻¹) gμ :=
    (hIpow.sub (integrable_const _)).mul_const _
  have key : ∫ z, (W.toFun z.1 z.2 - rStar d) ∂gμ
      = ∫ z, (((W.toFun z.1 z.2) ^ d - rStar d ^ d) * ((d : ℝ) * rStar d ^ (d - 1))⁻¹
          - Rd d (W.toFun z.1 z.2)) ∂gμ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show W.toFun z.1 z.2 - rStar d
        = ((W.toFun z.1 z.2) ^ d - rStar d ^ d) * ((d : ℝ) * rStar d ^ (d - 1))⁻¹
          - Rd d (W.toFun z.1 z.2)
    rw [sub_rStar_eq hd, div_eq_mul_inv]
  rw [integral_sub hIW (integrable_const _), integral_const] at key
  rw [integral_sub hIscaled hIrd, integral_mul_const,
    integral_sub hIpow (integrable_const _), integral_const] at key
  simp only [measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, measureReal_def] at key
  rw [div_eq_mul_inv]
  exact key

/-! ## The cost comparison -/

/-- **`eq:graphon-cost-decomposition`, in exact form.**  For any two graphons and any
`p ∈ (0,1)`, with `Λ = ℓ(p) - ℓ(p_*)`,

`I_p(W) - I_p(W') = (β_d + Λ/(d r_*^{d-1}))(∫W^d - ∫W'^d) + (∫Γ_d(W) - ∫Γ_d(W'))
                     - Λ(∫R_d(W) - ∫R_d(W'))`.

No inequality and no smallness is involved: this is the identity that the two halves of
`eq:endpoint-supporting-gap` and the edge/moment identity combine to. -/
theorem Ip_sub_Ip_eq (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (W W' : Graphon) :
    W.Ip p - W'.Ip p
      = (betaD d + (ell p - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1)))
          * (W.Wmoment d - W'.Wmoment d)
        + (GamInt d W - GamInt d W')
        - (ell p - ell (pStar d)) * (RdInt d W - RdInt d W') := by
  have hW := Ip_eq_Ip_pStar_add hd hp0 hp1 W
  have hW' := Ip_eq_Ip_pStar_add hd hp0 hp1 W'
  have hsW := Ip_pStar_eq_moment_add_gam hd W
  have hsW' := Ip_pStar_eq_moment_add_gam hd W'
  have heW := edge_eq_moment_sub_rdInt hd W
  have heW' := edge_eq_moment_sub_rdInt hd W'
  have hden : ((d : ℝ) * rStar d ^ (d - 1)) ≠ 0 := by
    have := dpos hd
    have := pow_pos (rStar_pos hd) (d - 1)
    positivity
  rw [hW, hW', hsW, hsW']
  have hEW : W.edgeDensity
      = rStar d + (W.Wmoment d - rStar d ^ d) / ((d : ℝ) * rStar d ^ (d - 1))
        - RdInt d W := by linarith
  have hEW' : W'.edgeDensity
      = rStar d + (W'.Wmoment d - rStar d ^ d) / ((d : ℝ) * rStar d ^ (d - 1))
        - RdInt d W' := by linarith
  rw [hEW, hEW']
  field_simp
  ring

/-- The inequality form actually used in `lem:localization-rank-one`: if `W` costs
no more than `W'` then the left-hand side of `eq:graphon-cost-decomposition` is bounded by
its right-hand side. -/
theorem localization_basic (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {W W' : Graphon} (hcost : W.Ip p ≤ W'.Ip p) :
    (betaD d + (ell p - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1)))
        * (W.Wmoment d - W'.Wmoment d) + GamInt d W
      ≤ GamInt d W' + (ell p - ell (pStar d)) * (RdInt d W - RdInt d W') := by
  have h := Ip_sub_Ip_eq hd hp0 hp1 W W'
  linarith [h, sub_nonpos.mpr hcost]

/-! ## The two integral estimates -/

/-- `(∫f)² ≤ ∫f²` on the probability space `gμ`, by expanding the variance.  Mathlib's
`ProbabilityTheory.variance_nonneg` is stated through `MemLp X 2 μ` rather than the two
`Integrable` hypotheses wanted here. -/
theorem sq_integral_le_integral_sq {f : ℝ × ℝ → ℝ} (hf : Integrable f gμ)
    (hf2 : Integrable (fun z => f z ^ 2) gμ) :
    (∫ z, f z ∂gμ) ^ 2 ≤ ∫ z, f z ^ 2 ∂gμ := by
  set c : ℝ := ∫ z, f z ∂gμ with hc
  have h0 : 0 ≤ ∫ z, (f z - c) ^ 2 ∂gμ := integral_nonneg fun z => sq_nonneg _
  have hpt : ∀ z, (f z - c) ^ 2 = f z ^ 2 - 2 * c * f z + c ^ 2 := fun z => by ring
  have hIlin : Integrable (fun z : ℝ × ℝ => 2 * c * f z) gμ := hf.const_mul _
  have hIsub : Integrable (fun z : ℝ × ℝ => f z ^ 2 - 2 * c * f z) gμ := hf2.sub hIlin
  have hexp : ∫ z, (f z - c) ^ 2 ∂gμ = (∫ z, f z ^ 2 ∂gμ) - c ^ 2 := by
    rw [integral_congr_ae (g := fun z : ℝ × ℝ => f z ^ 2 - 2 * c * f z + c ^ 2)
      (Filter.Eventually.of_forall hpt)]
    rw [integral_add hIsub (integrable_const _), integral_sub hf2 hIlin,
      integral_const_mul, integral_const]
    simp only [measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, measureReal_def]
    rw [← hc]; ring
  linarith [hexp ▸ h0]

/-- **`R_d² ≤ C_dΓ_d` integrated**, the paper's `𝒱_R² ≤ ∫R_d(W)² ≤ C_d 𝒢_Γ`. -/
theorem RdInt_sq_le_gamInt (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : Graphon, RdInt d W ^ 2 ≤ C * GamInt d W := by
  obtain ⟨C, hC0, hC⟩ := exists_rd_sq_le_gam hd
  refine ⟨C, hC0, fun W => ?_⟩
  have hIrd : Integrable (fun z : ℝ × ℝ => Rd d (W.toFun z.1 z.2)) gμ := integrable_Rd d W
  have hIrd2 : Integrable (fun z : ℝ × ℝ => Rd d (W.toFun z.1 z.2) ^ 2) gμ :=
    W.integrable_comp ((measurable_Rd d).pow_const 2)
      ((continuous_Rd d).pow 2).continuousOn
  have hIgam : Integrable (fun z : ℝ × ℝ => Gam d (W.toFun z.1 z.2)) gμ := integrable_Gam hd W
  have h1 : RdInt d W ^ 2 ≤ ∫ z, Rd d (W.toFun z.1 z.2) ^ 2 ∂gμ :=
    sq_integral_le_integral_sq hIrd hIrd2
  have h2 : ∫ z, Rd d (W.toFun z.1 z.2) ^ 2 ∂gμ ≤ ∫ z, C * Gam d (W.toFun z.1 z.2) ∂gμ := by
    refine integral_mono hIrd2 (hIgam.const_mul C) fun z => ?_
    exact hC _ (W.mem_Icc z.1 z.2)
  rw [integral_const_mul] at h2
  exact le_trans h1 h2

/-- **`eq:endpoint-gap-quartic-bound` integrated**: `c·∫|W - r_*|⁴ ≤ ∫Γ_d(W)`.  This is
what converts a bound on the singular endpoint gap into `eq:graphon-quartic-localization`. -/
theorem integral_dist_pow_four_le_gamInt (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ W : Graphon,
      c * ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ ≤ GamInt d W := by
  obtain ⟨c, hc0, hc⟩ := exists_gam_quartic_lower hd
  refine ⟨c, hc0, fun W => ?_⟩
  have hcont : Continuous fun x : ℝ => |x - rStar d| ^ 4 :=
    ((continuous_id.sub continuous_const).abs).pow 4
  have hI4 : Integrable (fun z : ℝ × ℝ => |W.toFun z.1 z.2 - rStar d| ^ 4) gμ :=
    W.integrable_comp hcont.measurable hcont.continuousOn
  have hIgam : Integrable (fun z : ℝ × ℝ => Gam d (W.toFun z.1 z.2)) gμ := integrable_Gam hd W
  have h : ∫ z, c * |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ
      ≤ ∫ z, Gam d (W.toFun z.1 z.2) ∂gμ := by
    refine integral_mono (hI4.const_mul c) hIgam fun z => ?_
    exact hc _ (W.mem_Icc z.1 z.2)
  rwa [integral_const_mul] at h

end SingularEndpoint

end UpperTailOptimizers
