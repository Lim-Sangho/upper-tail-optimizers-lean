import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs
import UpperTailOptimizers.Preliminaries.Graphons.ExternalInputs

/-!
# The singular endpoint scalar identities (Section 5, `paper/sections/singular.tex`)

The two *exact* identities on which the whole localization argument of
`sec:localization-rank-one` runs, together with their graphon integrals.

The first, `eq:endpoint-supporting-gap`, is the definition of the singular endpoint
supporting gap `Γ_d` read as a decomposition of the cost at the singular endpoint parameter `p_*`:

`I_{p_*}(W) = J_{p_*}(r_*) + β_d (∫W^d - r_*^d) + ∫Γ_d(W)`.

The second, `eq:entropy-parameter-shift` and its graphon integral — the second half of the same
display `eq:endpoint-supporting-gap` — says that moving
the ambient parameter off `p_*` changes the cost by an *affine* function of the edge
density:

`I_p(W) = I_{p_*}(W) + Λ_p·e(W) + C_p`,  `Λ_p = ℓ(p) - ℓ(p_*)`, `C_p = J_p(0) - J_{p_*}(0)`.

Neither is an approximation: both hold for every graphon and every `p ∈ (0,1)`.  Together
they replace the ordinary two-contact supporting line at the singular endpoint.

## Contents

* `GamInt` — the graphon integral `∫Γ_d(W)`; its nonnegativity `gamInt_nonneg` is in
  `SingularEndpoint/LocalizationRankOne/L4Bound.lean`;
* `Jp_eq_Jp_pStar_add` — the scalar displacement `eq:entropy-parameter-shift`;
* `Ip_eq_Ip_pStar_add` — its graphon integral, the second half of
  `eq:endpoint-supporting-gap`;
* `Jp_pStar_eq_gam` — the pointwise form of `eq:endpoint-supporting-gap`;
* `Ip_pStar_eq_moment_add_gam` — `eq:endpoint-supporting-gap` itself;
* `measurable_Gam` — measurability of `Γ_d`, shared with `SingularEndpoint/GraphonComparison/GraphonComparison.lean`;
* `integrable_Gam` — `Γ_d ∘ W` is `gμ`-integrable for every graphon;
* `Ip_sub_Jp_eq` — the cost gap of an arbitrary graphon against `J_p(r)`, from which
  `eq:constant-comparison-identity` is specialised in `SingularEndpoint/ConstantGraphonComparison/CostGap.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Real

variable {d : ℕ}

/-! ## Integrability of `Γ_d ∘ W` -/

/-- `Γ_d` is measurable: it is built from `J_{p_*}` and a monomial. -/
theorem measurable_Gam (d : ℕ) : Measurable (Gam d) := by
  unfold Gam
  exact ((measurable_Jp (pStar d)).sub measurable_const).sub
    (((measurable_id.pow_const d).sub measurable_const).const_mul _)

private theorem continuousOn_Gam_Icc (hd : 2 ≤ d) :
    ContinuousOn (Gam d) (Set.Icc 0 1) := by
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  unfold Gam
  exact ((continuousOn_Jp_Icc hp0 hp1).sub continuousOn_const).sub
    (continuousOn_const.mul ((continuousOn_pow d).sub continuousOn_const))

/-- The graphon integral `∫Γ_d(W)` of `sec:localization-rank-one`. -/
noncomputable def GamInt (d : ℕ) (W : Graphon) : ℝ :=
  ∫ z, Gam d (W.toFun z.1 z.2) ∂gμ

theorem integrable_Gam (hd : 2 ≤ d) (W : Graphon) :
    Integrable (fun z : ℝ × ℝ => Gam d (W.toFun z.1 z.2)) gμ :=
  W.integrable_comp (measurable_Gam d) (continuousOn_Gam_Icc hd)

/-! ## The `p`-displacement -/

/-- **`eq:entropy-parameter-shift`**: the entropy density depends on `p` through an affine
function of its argument,
`J_p(z) = J_{p_*}(z) + Λ_p z + C_p` with `Λ_p = ℓ(p) - ℓ(p_*)` and `C_p = J_p(0) - J_{p_*}(0)`.

Valid on the whole of `[0,1]`, endpoints included. -/
theorem Jp_eq_Jp_pStar_add (hd : 2 ≤ d) {p z : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Jp p z = Jp (pStar d) z + (ell p - ell (pStar d)) * z + (Jp p 0 - Jp (pStar d) 0) := by
  have hs0 : 0 < pStar d := pStar_pos hd
  have hs1 : pStar d < 1 := pStar_lt_one hd
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1pne : (1 : ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  have hsne : pStar d ≠ 0 := ne_of_gt hs0
  have h1sne : (1 : ℝ) - pStar d ≠ 0 := ne_of_gt (by linarith)
  rw [Jp_eq_entIntegrand hp0 hp1 hz0 hz1, Jp_eq_entIntegrand hs0 hs1 hz0 hz1,
    Jp_eq_entIntegrand hp0 hp1 le_rfl zero_le_one,
    Jp_eq_entIntegrand hs0 hs1 le_rfl zero_le_one,
    ell, ell, Real.log_div h1pne hpne, Real.log_div h1sne hsne]
  ring

/-- **The second half of `eq:endpoint-supporting-gap`**:
the graphon form of the displacement, `I_p(W) = I_{p_*}(W) + Λ_p·e(W) + C_p`.  The paper
now defines `Λ_h := ℓ(p_h) - ℓ_*` and `C_h := J_{p_h}(0) - J_{p_*}(0)` inline, just above
the display. -/
theorem Ip_eq_Ip_pStar_add (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (W : Graphon) :
    W.Ip p = W.Ip (pStar d) + (ell p - ell (pStar d)) * W.edgeDensity
      + (Jp p 0 - Jp (pStar d) 0) := by
  have hs0 : 0 < pStar d := pStar_pos hd
  have hs1 : pStar d < 1 := pStar_lt_one hd
  have hIs : Integrable (fun z : ℝ × ℝ => Jp (pStar d) (W.toFun z.1 z.2)) gμ :=
    W.integrable_comp (measurable_Jp _) (continuousOn_Jp_Icc hs0 hs1)
  have hIW : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2) gμ := W.integrable_self
  have hIlin : Integrable
      (fun z : ℝ × ℝ => (ell p - ell (pStar d)) * W.toFun z.1 z.2) gμ := hIW.const_mul _
  have hIsum : Integrable
      (fun z : ℝ × ℝ => Jp (pStar d) (W.toFun z.1 z.2)
        + (ell p - ell (pStar d)) * W.toFun z.1 z.2) gμ := hIs.add hIlin
  have hpt : ∀ z : ℝ × ℝ, Jp p (W.toFun z.1 z.2)
      = Jp (pStar d) (W.toFun z.1 z.2) + (ell p - ell (pStar d)) * W.toFun z.1 z.2
        + (Jp p 0 - Jp (pStar d) 0) := fun z =>
    Jp_eq_Jp_pStar_add hd hp0 hp1 (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2)
  show ∫ z, Jp p (W.toFun z.1 z.2) ∂gμ = _
  simp_rw [hpt]
  rw [integral_add hIsum (integrable_const _), integral_add hIs hIlin,
    integral_const_mul, integral_const]
  simp [Graphon.Ip, Graphon.edgeDensity]

/-! ## The singular endpoint decomposition -/

/-- The pointwise form of `eq:endpoint-supporting-gap`: by the definition of `Γ_d`,
`J_{p_*}(z) = J_{p_*}(r_*) + β_d (z^d - r_*^d) + Γ_d(z)`. -/
theorem Jp_pStar_eq_gam (d : ℕ) (z : ℝ) :
    Jp (pStar d) z = Jp (pStar d) (rStar d) + betaD d * (z ^ d - rStar d ^ d) + Gam d z := by
  rw [Gam]; ring

/-- **`eq:endpoint-supporting-gap`**, the exact singular endpoint identity
`I_{p_*}(W) = J_{p_*}(r_*) + β_d (∫W^d - r_*^d) + ∫Γ_d(W)`. -/
theorem Ip_pStar_eq_moment_add_gam (hd : 2 ≤ d) (W : Graphon) :
    W.Ip (pStar d)
      = Jp (pStar d) (rStar d) + betaD d * (W.Wmoment d - rStar d ^ d) + GamInt d W := by
  have hIpow : Integrable (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d) gμ :=
    W.integrable_comp (continuous_pow d).measurable (continuous_pow d).continuousOn
  have hIgam : Integrable (fun z : ℝ × ℝ => Gam d (W.toFun z.1 z.2)) gμ := integrable_Gam hd W
  have hIsub : Integrable
      (fun z : ℝ × ℝ => (W.toFun z.1 z.2) ^ d - rStar d ^ d) gμ :=
    hIpow.sub (integrable_const _)
  have hImul : Integrable
      (fun z : ℝ × ℝ => betaD d * ((W.toFun z.1 z.2) ^ d - rStar d ^ d)) gμ :=
    hIsub.const_mul _
  have hIaff : Integrable
      (fun z : ℝ × ℝ => Jp (pStar d) (rStar d)
        + betaD d * ((W.toFun z.1 z.2) ^ d - rStar d ^ d)) gμ :=
    (integrable_const _).add hImul
  have haff : ∫ z : ℝ × ℝ, (Jp (pStar d) (rStar d)
        + betaD d * ((W.toFun z.1 z.2) ^ d - rStar d ^ d)) ∂gμ
      = Jp (pStar d) (rStar d) + betaD d * (W.Wmoment d - rStar d ^ d) := by
    rw [integral_add (integrable_const _) hImul, integral_const_mul,
      integral_sub hIpow (integrable_const _), integral_const, integral_const]
    simp only [measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, measureReal_def]
    rfl
  show ∫ z, Jp (pStar d) (W.toFun z.1 z.2) ∂gμ = _
  -- `simp_rw` would loop here: the right-hand side of `Jp_pStar_eq_gam` again contains
  -- `J_{p_*}` evaluated at `r_*`.
  rw [integral_congr_ae (g := fun z : ℝ × ℝ =>
      (Jp (pStar d) (rStar d) + betaD d * ((W.toFun z.1 z.2) ^ d - rStar d ^ d))
        + Gam d (W.toFun z.1 z.2))
    (Filter.Eventually.of_forall fun z => Jp_pStar_eq_gam d _),
    integral_add hIaff hIgam, haff]
  rfl

/-- The cost gap against the constant graphon at a general parameter `p`, in the form
`eq:constant-comparison-identity` uses it:
`I_p(W) - J_p(r) = ∫Γ_d(W) - Γ_d(r) + β_d(∫W^d - r^d) + Λ_p(e(W) - r)`. -/
theorem Ip_sub_Jp_eq (hd : 2 ≤ d) {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (W : Graphon) :
    W.Ip p - Jp p r
      = (GamInt d W - Gam d r) + betaD d * (W.Wmoment d - r ^ d)
        + (ell p - ell (pStar d)) * (W.edgeDensity - r) := by
  rw [Ip_eq_Ip_pStar_add hd hp0 hp1 W, Ip_pStar_eq_moment_add_gam hd W,
    Jp_eq_Jp_pStar_add hd hp0 hp1 hr0 hr1, Jp_pStar_eq_gam d r]
  ring

end SingularEndpoint

end UpperTailOptimizers
