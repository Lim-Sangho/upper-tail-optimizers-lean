import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.CostRemainder
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.Localization

/-!
# Comparison with the constant graphon

`lem:constant-graphon-comparison` of `paper/paper.tex` in one statement: for small `h > 0` the
edge and cost expansions of `constant_graphon_comparison` hold, the constant graphon `W ≡ r_h` is
feasible but has strictly larger `I_{p_h}`-value, and consequently `p_h < pc(r_h)`.

The threshold and the remainder constant depend only on the family `B`, hence only on `d`; the
graph `H` is quantified afterwards.  The last clause uses the axiom `lubetzkyZhao`, as in
`singular_endpoint_symmetry_breaking`.

`graphon_cost_decomposition` is `eq:graphon-cost-decomposition`, the same comparison with an
arbitrary graphon `W` in place of the constant graphon.
-/

namespace UpperTailOptimizers

open Filter Topology

variable {d : ℕ}

/-- **`lem:constant-graphon-comparison`.**  There are `C, δ > 0`, depending only on the family
`B`, such that for `|h| < δ`

  `e(W_h) = r_h - (d-1)h² + O_d(h⁴)`,   `I_{p_h}(W_h) = J_{p_h}(r_h) - \frac{d³}{3}h⁴ + O_d(h⁶)`,

and for every `d`-regular `H` and `0 < h < δ` the constant graphon `W ≡ r_h` is feasible, has
strictly larger `I_{p_h}`-value than `W_h`, and `p_h < pc(r_h)`. -/
theorem constant_graphon_comparison_full (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      (∀ (h : ℝ) (hh : |h| < B.h₀), |h| < δ →
        |(B.graphon hh).edgeDensity - (B.rVal h - ((d : ℝ) - 1) * h ^ 2)| ≤ C * |h| ^ 4 ∧
        |(B.graphon hh).Ip (B.p h) - (Jp (B.p h) (B.rVal h) - (d : ℝ) ^ 3 / 3 * h ^ 4)|
          ≤ C * |h| ^ 6) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ v, H.degree v = d) → 1 ≤ H.edgeFinset.card →
        ∀ (h : ℝ) (hh : |h| < B.h₀), 0 < h → h < δ →
          ∀ hr : B.rVal h ∈ Set.Icc (0:ℝ) 1,
            Feasible H (B.rVal h) (constGraphon (B.rVal h) hr) ∧
            (B.graphon hh).Ip (B.p h) < (constGraphon (B.rVal h) hr).Ip (B.p h) ∧
            B.p h < pcGlobal d (B.rVal h) := by
  obtain ⟨C, δ₀, hC, hδ₀, hexp⟩ := constant_graphon_comparison hd B
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
  refine ⟨C, min δ₀ (min δ₁ δ₂), hC, lt_min hδ₀ (lt_min hδ₁ hδ₂),
    fun h hh hδ => hexp h hh (lt_of_lt_of_le hδ (min_le_left _ _)), ?_⟩
  intro V _ _ H _ hreg hcard h hh hh0 hhδ hrI
  have hδ₁' : h < δ₁ := lt_of_lt_of_le hhδ ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₂' : h < δ₂ := lt_of_lt_of_le hhδ ((min_le_right _ _).trans (min_le_right _ _))
  have hp0 := (B.p_mem h hh).1
  have hp1 := (B.p_mem h hh).2
  have hr0 := KKTFamily.rVal_pos hd hh
  have hr1 := KKTFamily.rVal_lt_one hd hh
  have hlt : B.p h < B.rVal h := by
    refine hprop ?_ (ne_of_gt hh0)
    rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
    exact hδ₂'
  -- the constant graphon is feasible and costs `J_{p_h}(r_h)`
  have hcfeas : Feasible H (B.rVal h) (constGraphon (B.rVal h) hrI) :=
    le_of_eq (tDensity_constGraphon hrI H).symm
  have hcIp : (constGraphon (B.rVal h) hrI).Ip (B.p h) = Jp (B.p h) (B.rVal h) :=
    Ip_constGraphon hrI (B.p h)
  have hstrict := himp h hh hh0 hδ₁'
  refine ⟨hcfeas, hcIp ▸ hstrict, ?_⟩
  -- `W_h` is feasible, so `Φ_H(p_h,r_h) < J_{p_h}(r_h)`; no supporting line, hence `p_h < pc(r_h)`
  have hfeas : Feasible H (B.rVal h) (B.graphon hh) := by
    rw [Feasible, KKTFamily.graphon_tDensity_eq_rVal_pow H hd hreg hh]
  have hphi : phiVar H (B.p h) (B.rVal h) < Jp (B.p h) (B.rVal h) :=
    lt_of_le_of_lt (csInf_le (phiVar_bddBelow H hp0 hp1) ⟨B.graphon hh, hfeas, rfl⟩) hstrict
  have hno : ¬ ∃ a : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Jp (B.p h) (B.rVal h) + a * (x - B.rVal h ^ d) ≤ phi (B.p h) d x := fun hsupp =>
    absurd ((lubetzkyZhao H hd hreg hcard hp0 hlt hr1).mpr hsupp) (ne_of_lt hphi)
  by_contra hcon
  push Not at hcon
  exact hno ((lz_boundary_M2_global hd hr0 hr1 hp0 hp1).mpr hcon)

/-- **`eq:graphon-cost-decomposition`.**  For every graphon `W` and `|h| < h₀`, with
`Λ_h = ℓ(p_h) - ℓ(p_*)`,

`I_{p_h}(W) - I_{p_h}(W_h) = ∫Γ_d(W) - ∫Γ_d(W_h) + β_d(∫W^d - r_h^d) + Λ_h(e(W) - e(W_h))`. -/
theorem graphon_cost_decomposition (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (W : Graphon) :
    W.Ip (B.p h) - (B.graphon hh).Ip (B.p h)
      = GamInt d W - GamInt d (B.graphon hh) + betaD d * (W.Wmoment d - B.rVal h ^ d)
        + (ell (B.p h) - ell (pStar d)) * (W.edgeDensity - (B.graphon hh).edgeDensity) := by
  rw [Ip_sub_Ip_eq_edgeDensity hd (B.p_mem h hh).1 (B.p_mem h hh).2 W (B.graphon hh),
    KKTFamily.graphon_Wmoment_eq_rVal_pow hd hh]

end UpperTailOptimizers
