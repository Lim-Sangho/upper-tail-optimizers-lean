import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.EdgeGap
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.GamRVal
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyContinuity
import UpperTailOptimizers.Preliminaries.Graphons.Attainment

/-!
# Strict improvement over the constant graphon (Section 5, `paper/sections/singular.tex`)

`lem:constant-graphon-comparison` is the assertion that the
symmetry-breaking candidate beats the constant graphon of the same `H`-density:

  `I_{p_h}(W_h) - J_{p_h}(r_h) = -\frac{d³}{3}h⁴ + O_d(h⁶)`,

and in particular that the difference is **negative** for all sufficiently small `h > 0`, and
consequently that `p_h < pc(r_h)`: `(p_h, r_h)` lies in the symmetry-breaking phase.

The exact identity `eq:constant-comparison-identity` is `cost_gap_eq`,

  `I_{p_h}(W_h) - J_{p_h}(r_h) = \left(∫Γ_d(W_h) - Γ_d(r_h)\right) + Λ_h\{e(W_h) - r_h\}`,

and its two brackets are now both known:

* `tendsto_gamInt_sub_gamRVal` (`SingularEndpoint/ConstantGraphonComparison/GamRVal.lean`): the first is `\frac{d³}{3}h⁴ + o(h⁴)`.
  It needed only `α_h → 1/2`;
* `tendsto_ell_coeff` with `Lcoeff_eq` gives `Λ_h = \frac{2d³}{3(d-1)}h² + o(h²)`
  (the `Λ_h` entry of `eq:rank-one-parameter-expansions`), and `tendsto_edge_gap` gives
  `e(W_h) - r_h = -(d-1)h² + o(h²)` (unlabelled in the proof of `lem:constant-graphon-comparison`),
  so the second bracket is `-\frac{2d³}{3}h⁴ + o(h⁴)`.

The total is `-\frac{d³}{3}h⁴ + o(h⁴)`, which gives the sign.  The paper's sharper `O_d(h⁶)`
remainder, which comes from evenness in `h`, is `constant_graphon_comparison` in
`SingularEndpoint/ConstantGraphonComparison/CostRemainder.lean`.

## Contents

* `tendsto_cost_gap` — `(I_{p_h}(W_h) - J_{p_h}(r_h))/h⁴ → -d³/3`;
* `singular_endpoint_strict_improvement` — `I_{p_h}(W_h) < J_{p_h}(r_h)` for all small `h > 0`, i.e.
  the strictness clause of `lem:constant-graphon-comparison`;
* `singular_endpoint_symmetry_breaking` — its consequence `p_h < pc(r_h)`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology MeasureTheory

variable {d : ℕ}

/-- **`lem:constant-graphon-comparison`, to leading order**:

  `\frac{I_{p_h}(W_h) - J_{p_h}(r_h)}{h⁴} \to -\frac{d³}{3}`.

`W_h = B.graphon hh` depends on a proof `hh : |h| < h₀`, so — exactly as in
`tendsto_gamInt_graphon` — the cost gap is represented by an arbitrary `K : ℝ → ℝ` agreeing
with it on the window. -/
theorem tendsto_cost_gap (hd : 2 ≤ d) (B : KKTFamily d) {K : ℝ → ℝ}
    (hK : ∀ (h : ℝ) (hh : |h| < B.h₀),
      K h = (B.graphon hh).Ip (B.p h) - Jp (B.p h) (B.rVal h)) :
    Tendsto (fun h : ℝ => K h / h ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 (-((d : ℝ) ^ 3 / 3))) := by
  classical
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  -- representatives for the two brackets
  set F : ℝ → ℝ := fun h => if hh : |h| < B.h₀ then GamInt d (B.graphon hh) else 0 with hFdef
  set G : ℝ → ℝ := fun h => if hh : |h| < B.h₀ then (B.graphon hh).edgeDensity else 0 with hGdef
  have hF : ∀ (h : ℝ) (hh : |h| < B.h₀), F h = GamInt d (B.graphon hh) := fun h hh => dif_pos hh
  have hG : ∀ (h : ℝ) (hh : |h| < B.h₀), G h = (B.graphon hh).edgeDensity := fun h hh =>
    dif_pos hh
  have hGam := tendsto_gamInt_sub_gamRVal hd B hF
  have hEdge := graphon_edge_gap B hd hG
  have hLam := (tendsto_ell_coeff B hd).2
  have hprod := hLam.mul hEdge
  have hsum := hGam.add hprod
  have hval : (d : ℝ) ^ 3 / 3 + Lcoeff B * -((d : ℝ) - 1) = -((d : ℝ) ^ 3 / 3) := by
    rw [Lcoeff_eq B hd]
    field_simp
    ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_window B] with h hh hw
  have hne : h ≠ 0 := hh
  rw [hK h hw, KKTFamily.cost_gap_eq hd hw, ← hF h hw, ← hG h hw]
  field_simp

/-- **The strictness clause of `lem:constant-graphon-comparison`**: the symmetry-breaking optimizer strictly
beats the constant graphon of the same `H`-density, for every small enough `h > 0` — the
lemma's closing sentence that the constant graphon `W ≡ r_h` "is feasible but has strictly
larger `I_{p_h}`-value".

The constant graphon `W ≡ r_h` is feasible because its `H`-density is `r_h^m`, the value that
`W_h` also attains (`graphon_tDensity_eq_rVal_pow`), so this places `(p_h, r_h)` in the
symmetry-breaking phase; the lemma's consequence `p_h < pc(r_h)` is
`singular_endpoint_symmetry_breaking`. -/
theorem singular_endpoint_strict_improvement (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ δ > 0, ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
      (B.graphon hh).Ip (B.p h) < Jp (B.p h) (B.rVal h) := by
  classical
  set K : ℝ → ℝ := fun h =>
    if hh : |h| < B.h₀ then (B.graphon hh).Ip (B.p h) - Jp (B.p h) (B.rVal h) else 0 with hKdef
  have hK : ∀ (h : ℝ) (hh : |h| < B.h₀),
      K h = (B.graphon hh).Ip (B.p h) - Jp (B.p h) (B.rVal h) := fun h hh => dif_pos hh
  have hlim := tendsto_cost_gap hd B hK
  have hneg : (-((d : ℝ) ^ 3 / 3) : ℝ) < 0 := by
    have : (0 : ℝ) < (d : ℝ) ^ 3 := by positivity
    linarith
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), K h / h ^ 4 < 0 := hlim.eventually_lt_const hneg
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hmem⟩ := hev
  refine ⟨δ, hδ, fun h hh hpos hlt => ?_⟩
  have hdist : dist h (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]; exact hlt
  have hq := hmem hdist (ne_of_gt hpos)
  have h4 : (0 : ℝ) < h ^ 4 := by positivity
  have hKneg : K h < 0 := by
    by_contra hc
    push Not at hc
    have : (0 : ℝ) ≤ K h / h ^ 4 := div_nonneg hc h4.le
    linarith
  rw [hK h hh] at hKneg
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`p_h < p_c(r_h)`**: the symmetry-breaking parameters lie strictly on the symmetry-breaking side
of the Lubetzky–Zhao boundary.

`lem:constant-graphon-comparison` (`singular_endpoint_strict_improvement`) says the symmetry-breaking optimizer
beats the constant graphon of the same `H`-density, so `Φ_H(p_h, r_h) < J_{p_h}(r_h)`; the
Lubetzky–Zhao dichotomy then denies a supporting line at `r_h^d`, and `lz_boundary_M2_global`
converts that into `p_h < p_c(r_h)`.

This is the clause `p_h < pc(r_h)` of `thm:singular-endpoint` and `thm:endpoint-optimizers`,
recorded in the `below_boundary` field of `SingularEndpointOptimizers`; it is the one singular endpoint
statement that uses the `lubetzkyZhao` axiom. -/
theorem singular_endpoint_symmetry_breaking (hd : 2 ≤ d) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hcard : 1 ≤ H.edgeFinset.card) (B : KKTFamily d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < B.h₀ → 0 < h → h < δ →
      B.p h < pcGlobal d (B.rVal h) := by
  obtain ⟨δ₁, hδ₁, himp⟩ := singular_endpoint_strict_improvement hd B
  -- `p_h < r_h` for small `h`, since `p_* < r_*`
  have hmid : pStar d < (pStar d + rStar d) / 2 ∧ (pStar d + rStar d) / 2 < rStar d := by
    have := pStar_lt_rStar hd; constructor <;> linarith
  have hp : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), B.p h < (pStar d + rStar d) / 2 :=
    ((KKTFamily.tendsto_p B).mono_left nhdsWithin_le_nhds).eventually_lt_const hmid.1
  have hr : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), (pStar d + rStar d) / 2 < B.rVal h :=
    (tendsto_rVal hd B).eventually_const_lt hmid.2
  have hpr : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), B.p h < B.rVal h := by
    filter_upwards [hp, hr] with h h1 h2 using lt_trans h1 h2
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hpr
  obtain ⟨δ₂, hδ₂, hprop⟩ := hpr
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun h hh hh0 hhδ => ?_⟩
  have hp0 := (B.p_mem h hh).1
  have hp1 := (B.p_mem h hh).2
  have hr0 := KKTFamily.rVal_pos hd hh
  have hr1 := KKTFamily.rVal_lt_one hd hh
  have hdist : dist h (0 : ℝ) < δ₂ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
    exact lt_of_lt_of_le hhδ (min_le_right _ _)
  have hlt : B.p h < B.rVal h := hprop hdist (ne_of_gt hh0)
  -- `W_h` is feasible, and strictly cheaper than the constant graphon
  have hfeas : Feasible H (B.rVal h) (B.graphon hh) := by
    rw [Feasible, KKTFamily.graphon_tDensity_eq_rVal_pow H hd hreg hh]
  have hphi : phiVar H (B.p h) (B.rVal h) < Jp (B.p h) (B.rVal h) :=
    lt_of_le_of_lt
      (csInf_le (phiVar_bddBelow H hp0 hp1) ⟨B.graphon hh, hfeas, rfl⟩)
      (himp h hh hh0 (lt_of_lt_of_le hhδ (min_le_left _ _)))
  -- no supporting line, hence `p_h` is below the boundary curve
  have hno : ¬ ∃ a : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Jp (B.p h) (B.rVal h) + a * (x - B.rVal h ^ d) ≤ phi (B.p h) d x := by
    intro hsupp
    exact absurd ((lubetzkyZhao H hd hreg hcard hp0 hlt hr1).mpr hsupp) (ne_of_lt hphi)
  by_contra hcon
  push Not at hcon
  exact hno ((lz_boundary_M2_global hd hr0 hr1 hp0 hp1).mpr hcon)


end SingularEndpoint

end UpperTailOptimizers
