import UpperTailOptimizers.SingularEndpoint.EdgeGap
import UpperTailOptimizers.SingularEndpoint.L4Bound

/-!
# `lem:localization-rank-one` along the family (Section 7, `paper/singular_endpoint.tex`)

`SingularEndpoint/L4Bound.lean` proves the coercive step of `lem:localization-rank-one` for an
**arbitrary** reference graphon `W'` saturating the moment:
`integral_dist_pow_four_localized` is `eq:graphon-quartic-localization` in the form

`c∫|W - r_*|⁴ ≤ 2(𝒢_{Γ,h} + |Λ_h||𝒱_{R,h}| + C_dΛ_h²/2)`.

What was missing there was the quantitative `O(h⁴)` input: the paper's `𝒢_{Γ,h} = O(h⁴)`,
`Λ_h = O(h²)` and `𝒱_{R,h} = O(h²)` hold *along the singular endpoint family*, and needed the
expansions `eq:rank-one-parameter-expansions`.  Those are now available, so this file performs
the instantiation and states the second display of `eq:graphon-quartic-localization`,

`∫|W - r_*|⁴ ≤ M h⁴`   for every competitor `W` at `(p_h, r_h)` that is at least as cheap
as `W_h`,

uniformly over `0 < h < δ`.

The three rates fed in are exactly the ones of `eq:rank-one-parameter-expansions`:

* `tendsto_gamInt_graphon` (`SingularEndpoint/GamAverage.lean`): `∫Γ_d(W_h)/h⁴ → d³/3`, so
  `𝒢_{Γ,h} = O(h⁴)`;
* `tendsto_ell_coeff` (`SingularEndpoint/FamilyQuadratic.lean`): `Λ_h/h² → ℓ₂` and `Λ_h → 0`, so
  `Λ_h = O(h²)` — and the second statement is what makes the coefficient
  `β_d + Λ_h/(d r_*^{d-1})` of `eq:graphon-cost-decomposition` stay above `β_d/2`, which is
  the `b₀` fed to `integral_dist_pow_four_localized`;
* `𝒱_{R,h} = O(h²)`: by the edge/moment identity (`edge_eq_moment_sub_rdInt`) and
  `∫∫W_h^d = r_h^d` (`graphon_Wmoment_eq_rVal_pow`),
  `𝒱_{R,h} = (r_h^d - r_*^d)/(d r_*^{d-1}) - (e(W_h) - r_*)`, and both brackets are `O(h²)`
  by `tendsto_rVal_coeff` and `graphon_edge_gap`.

Each rate converts to an eventual bound by `exists_eventual_bound` — a finite
limit for `f(h)/h^n` makes `|f(h)| ≤ Mh^n` on a punctured ball — and the four eventual
statements are merged into a single punctured ball by the `eventually_nhdsWithin_iff` +
`Metric.eventually_nhds_iff` idiom of `singular_endpoint_strict_improvement`.

## Contents

* `family_localization` — `eq:graphon-quartic-localization` along the family, `L⁴`;
* `family_localization_sq` — its `L²` companion, by Cauchy–Schwarz on `gμ`;
* `exists_eventual_bound` — the rate-to-eventual-bound device, shared with
  `SingularEndpoint/LdSharp.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter MeasureTheory Topology

variable {d : ℕ}

/-! ## From a rate to an eventual bound -/

/-- A function with a finite rate at the origin is `O(h^n)` on a punctured neighbourhood: if
`f(h)/h^n → L` along `𝓝[≠] 0` and `h^n > 0` off the origin, then `|f(h)| ≤ (|L| + 1)h^n`
eventually.  This is the only analytic content of the instantiation below — every ingredient
of `eq:rank-one-parameter-expansions` enters through it. -/
theorem exists_eventual_bound {f : ℝ → ℝ} {L : ℝ} {n : ℕ}
    (hpow : ∀ h : ℝ, h ≠ 0 → 0 < h ^ n)
    (hf : Tendsto (fun h : ℝ => f h / h ^ n) (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ h in 𝓝[≠] (0 : ℝ), |f h| ≤ M * h ^ n := by
  refine ⟨|L| + 1, by positivity, ?_⟩
  have hlt := hf.abs.eventually_lt_const (show |L| < |L| + 1 by linarith)
  filter_upwards [hlt, self_mem_nhdsWithin] with h hh hmem
  have hne : h ≠ 0 := hmem
  have hp : (0 : ℝ) < h ^ n := hpow h hne
  rw [abs_div, abs_of_pos hp] at hh
  exact ((div_lt_iff₀ hp).mp hh).le

/-! ## The `L⁴` localization along the family -/

/-- **`eq:graphon-quartic-localization`, second display, along the singular endpoint family.**

There are a constant `M > 0` and a width `δ > 0` such that for every `0 < h < δ` in the
family window, every graphon `W` that is feasible at `(p_h, r_h)` and costs no more than the
candidate `W_h` satisfies

`∫|W - r_*|⁴ ≤ M h⁴`.

This is `integral_dist_pow_four_localized` instantiated at `p := p_h`, `r := r_h`,
`W' := W_h`, with `b₀ := β_d/2` — legitimate because `Λ_h → 0`, so the coefficient
`β_d + Λ_h/(d r_*^{d-1})` of `eq:graphon-cost-decomposition` eventually exceeds `β_d/2` —
and with the three family rates of `eq:rank-one-parameter-expansions` supplying
`𝒢_{Γ,h} ≤ M₁h⁴`, `|Λ_h| ≤ M₂h²` and `|𝒱_{R,h}| ≤ M₃h²`. -/
theorem family_localization (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ ≤ M * h ^ 4 := by
  classical
  obtain ⟨Cc, hCc0, hVG⟩ := RdInt_sq_le_gamInt (d := d) hd
  obtain ⟨c, hc0, hcG⟩ := integral_dist_pow_four_le_gamInt (d := d) hd
  -- Arbitrary representatives of the three `h`-dependent family quantities.
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ (h : ℝ) (hh : |h| < B.h₀), F h = GamInt d (B.graphon hh) :=
    ⟨fun h => if hh : |h| < B.h₀ then GamInt d (B.graphon hh) else 0, fun _ hh => dif_pos hh⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ,
      ∀ (h : ℝ) (hh : |h| < B.h₀), G h = (B.graphon hh).edgeDensity :=
    ⟨fun h => if hh : |h| < B.h₀ then (B.graphon hh).edgeDensity else 0, fun _ hh => dif_pos hh⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, ∀ (h : ℝ) (hh : |h| < B.h₀), R h = RdInt d (B.graphon hh) :=
    ⟨fun h => if hh : |h| < B.h₀ then RdInt d (B.graphon hh) else 0, fun _ hh => dif_pos hh⟩
  -- `𝒢_{Γ,h}/h⁴ → d³/3`.
  have hFlim : Tendsto (fun h : ℝ => F h / h ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 ((d : ℝ) ^ 3 / 3)) :=
    tendsto_gamInt_graphon hd B hF
  -- `(r_h^d - r_*^d)/h²` converges, by the geometric-sum factorisation.
  have hrpow : Tendsto (fun h : ℝ => (B.rVal h ^ d - rStar d ^ d) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(2 * (4 * (d : ℝ) - 1) / 3) * ((d : ℝ) * rStar d ^ (d - 1)))) := by
    have hcof := tendsto_geom_sum₂ (f := B.rVal) (g := fun _ : ℝ => rStar d) d
      (tendsto_rVal hd B) tendsto_const_nhds
    refine ((tendsto_rVal_coeff B hd).mul hcof).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hmem
    have hne : h ≠ 0 := hmem
    rw [pow_sub_pow_eq (B.rVal h) (rStar d) d]
    field_simp
  -- `(e(W_h) - r_*)/h²` converges.
  have hedge : Tendsto (fun h : ℝ => (G h - rStar d) / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((d : ℝ) - 1) + -(2 * (4 * (d : ℝ) - 1) / 3))) := by
    refine ((graphon_edge_gap B hd hG).add (tendsto_rVal_coeff B hd)).congr'
      (Filter.Eventually.of_forall fun h => ?_)
    rw [← add_div]
    congr 1
    ring
  -- Hence `𝒱_{R,h}/h²` converges, by the edge/moment identity at the saturated moment.
  have hRlim : Tendsto (fun h : ℝ => R h / h ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(2 * (4 * (d : ℝ) - 1) / 3) * ((d : ℝ) * rStar d ^ (d - 1))
            / ((d : ℝ) * rStar d ^ (d - 1))
          - (-((d : ℝ) - 1) + -(2 * (4 * (d : ℝ) - 1) / 3)))) := by
    refine ((hrpow.div_const ((d : ℝ) * rStar d ^ (d - 1))).sub hedge).congr' ?_
    filter_upwards [eventually_window B] with h hw
    rw [hR h hw, hG h hw]
    have he := edge_eq_moment_sub_rdInt hd (B.graphon hw)
    rw [KKTFamily.graphon_Wmoment_eq_rVal_pow hd hw] at he
    rw [he, div_right_comm, div_sub_div_same, sub_sub_cancel]
  -- The three eventual bounds.
  obtain ⟨M₁, hM₁0, hM₁⟩ :=
    exists_eventual_bound (fun _ hne => Even.pow_pos (by norm_num) hne) hFlim
  obtain ⟨M₂, hM₂0, hM₂⟩ :=
    exists_eventual_bound (f := fun h : ℝ => ell (B.p h) - ell (pStar d)) (n := 2)
      (fun _ hne => Even.pow_pos (by norm_num) hne) ((tendsto_ell_coeff B hd).2)
  obtain ⟨M₃, hM₃0, hM₃⟩ :=
    exists_eventual_bound (fun _ hne => Even.pow_pos (by norm_num) hne) hRlim
  -- The coefficient of `eq:graphon-cost-decomposition` stays above `β_d/2`.
  have hbpos : 0 < betaD d := betaD_pos hd
  have hb0ev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), betaD d / 2 ≤ betaD d
      + (ell (B.p h) - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1)) := by
    have h0 : Tendsto
        (fun h : ℝ => |(ell (B.p h) - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1))|)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have h1 := ((tendsto_ell_coeff B hd).1.div_const ((d : ℝ) * rStar d ^ (d - 1))).abs
      simpa using h1
    filter_upwards [h0.eventually_lt_const (show (0 : ℝ) < betaD d / 2 by linarith)] with h hlt
    linarith [(abs_lt.mp hlt).1]
  -- Merge the four eventual statements into one punctured ball.
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      |F h| ≤ M₁ * h ^ 4 ∧ |ell (B.p h) - ell (pStar d)| ≤ M₂ * h ^ 2 ∧
        |R h| ≤ M₃ * h ^ 2 ∧ betaD d / 2 ≤ betaD d
          + (ell (B.p h) - ell (pStar d)) / ((d : ℝ) * rStar d ^ (d - 1)) := by
    filter_upwards [hM₁, hM₂, hM₃, hb0ev] with h a1 a2 a3 a4
    exact ⟨a1, a2, a3, a4⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hmem⟩ := hev
  have hnum : 0 < 2 * (M₁ + M₂ * M₃ + Cc * M₂ ^ 2 / 2) := by
    have h1 : 0 < M₂ * M₃ := mul_pos hM₂0 hM₃0
    have h2 : 0 < Cc * M₂ ^ 2 := mul_pos hCc0 (pow_pos hM₂0 2)
    linarith
  refine ⟨2 * (M₁ + M₂ * M₃ + Cc * M₂ ^ 2 / 2) / c, div_pos hnum hc0, δ, hδ, ?_⟩
  intro h hh hpos hlt W hfeas hcost
  have hdist : dist h (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact hlt
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hmem hdist (ne_of_gt hpos)
  have hp := B.p_mem h hh
  have h2 : (0 : ℝ) < h ^ 2 := pow_pos hpos 2
  have hkey := integral_dist_pow_four_localized hd H hreg hm hp.1 hp.2
    (KKTFamily.rVal_pos hd hh).le hfeas
    (KKTFamily.graphon_Wmoment_eq_rVal_pow hd hh) hcost
    (show (0 : ℝ) < betaD d / 2 by linarith) hCc0 hVG hb4 hc0 hcG
  rw [← hF h hh, ← hR h hh] at hkey
  have hM2h : (0 : ℝ) ≤ M₂ * h ^ 2 := (mul_pos hM₂0 h2).le
  have hGam : F h ≤ M₁ * h ^ 4 := le_trans (le_abs_self _) hb1
  have hprod : |ell (B.p h) - ell (pStar d)| * |R h| ≤ M₂ * h ^ 2 * (M₃ * h ^ 2) :=
    mul_le_mul hb2 hb3 (abs_nonneg _) hM2h
  have hsq : (ell (B.p h) - ell (pStar d)) ^ 2 ≤ (M₂ * h ^ 2) ^ 2 := by
    have habs := sq_abs (ell (B.p h) - ell (pStar d))
    nlinarith [abs_nonneg (ell (B.p h) - ell (pStar d)), hb2, hM2h]
  have hCcs : Cc * (ell (B.p h) - ell (pStar d)) ^ 2 / 2 ≤ Cc * (M₂ * h ^ 2) ^ 2 / 2 := by
    linarith [mul_le_mul_of_nonneg_left hsq hCc0.le]
  have hcomb : c * ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ
      ≤ 2 * (M₁ + M₂ * M₃ + Cc * M₂ ^ 2 / 2) * h ^ 4 := by
    linarith [hkey, hGam, hprod, hCcs]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  linarith [hcomb]

/-! ## The `L²` companion -/

/-- **`eq:graphon-quartic-localization`, first display, along the singular endpoint family**:
`∫|W - r_*|² ≤ M h²` under the same hypotheses as `family_localization`.

Cauchy–Schwarz on the probability space `gμ` applied to `f = |W - r_*|²` turns the `L⁴`
bound into an `L²` bound with constant `√M`. -/
theorem family_localization_sq (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
        ∀ W : Graphon, B.rVal h ^ H.edgeFinset.card ≤ W.tDensity H →
          W.Ip (B.p h) ≤ (B.graphon hh).Ip (B.p h) →
          ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 2 ∂gμ ≤ M * h ^ 2 := by
  obtain ⟨M, hM0, δ, hδ, hbd⟩ := family_localization hd H hreg hm B
  refine ⟨Real.sqrt M, Real.sqrt_pos.mpr hM0, δ, hδ, ?_⟩
  intro h hh hpos hlt W hfeas hcost
  have hcont : Continuous fun x : ℝ => |x - rStar d| ^ 2 :=
    ((continuous_id.sub continuous_const).abs).pow 2
  have hcont2 : Continuous fun x : ℝ => (|x - rStar d| ^ 2) ^ 2 := hcont.pow 2
  have hcs := sq_integral_le_integral_sq
    (W.integrable_comp hcont.measurable hcont.continuousOn)
    (W.integrable_comp hcont2.measurable hcont2.continuousOn)
  have h44 : ∫ z, (|W.toFun z.1 z.2 - rStar d| ^ 2) ^ 2 ∂gμ
      = ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 4 ∂gμ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  rw [h44] at hcs
  have hnn : 0 ≤ ∫ z, |W.toFun z.1 z.2 - rStar d| ^ 2 ∂gμ :=
    integral_nonneg fun z => sq_nonneg _
  have hrhs : (Real.sqrt M * h ^ 2) ^ 2 = M * h ^ 4 := by
    rw [mul_pow, Real.sq_sqrt hM0.le]; ring
  nlinarith [hcs, hbd h hh hpos hlt W hfeas hcost, hnn, hrhs,
    mul_pos (Real.sqrt_pos.mpr hM0) (pow_pos hpos 2)]

end SingularEndpoint

end UpperTailOptimizers
