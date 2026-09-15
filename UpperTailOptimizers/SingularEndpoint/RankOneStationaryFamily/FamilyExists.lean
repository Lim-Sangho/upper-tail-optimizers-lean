import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyDeriv
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyAnalytic
import UpperTailOptimizers.LZBoundary.AnalyticIFT

/-!
# Existence of the coalescing scalar family (Section 5, `paper/sections/singular.tex`)

The scalar half of `lem:rank-one-kkt-family`: there is a real-analytic family
`h ↦ (u_h, ℓ_h, γ_h)` through `(u_*, ℓ_*, γ_*)` solving the three rank-one KKT equations
`eq:three-value-kkt` for all small `h ≠ 0`.

Everything the analytic implicit function theorem needs is in place:

* `analyticAt_Fsys` (`SingularEndpoint/RankOneStationaryFamily/FamilyAnalytic.lean`) — joint analyticity of the
  desingularized system at the base point;
* `Fsys_base` (`SingularEndpoint/RankOneStationaryFamily/FamilyBase.lean`) — its vanishing there, which reduces to the
  contact identities `Lstar_rStar`, `Lstar1_rStar`, `Lstar2_rStar`;
* `exists_hasStrictFDerivAt_Fsys` (`SingularEndpoint/RankOneStationaryFamily/FamilyDeriv.lean`) — the base-point derivative,
  identified with the invertible `jac3` of `SingularEndpoint/RankOneStationaryFamily/Jacobian3.lean`.

So this file is the call, plus the transport back from the desingularized system
`(E₁, E₂, E₃)` to the three original equations by `lell_three_eq_iff`, which is legitimate
exactly for `h ≠ 0`.

**What this is not.** The remaining clauses of `lem:rank-one-kkt-family` — the
recovery of `p_h` from `ℓ_h` (explicitly, `p = 1/(1+e^ℓ)`), the block weight `α_h` from the
linear row-balance equation, the symmetries `u_{-h} = u_h` and `α_{-h} = 1 - α_h`, local
uniqueness, and the expansions `eq:rank-one-parameter-expansions` (now the separate
`lem:rank-one-parameter-expansions`) — are not proved here, so
this file alone does not build an `KKTFamily`.  They are supplied by
`SingularEndpoint/RankOneStationaryFamily/FamilySymm.lean` (the symmetries and the density `p_h`), `SingularEndpoint/RankOneStationaryFamily/Alpha.lean`
(`exists_family_with_block_weight`), `SingularEndpoint/RankOneStationaryFamily/FamilyUnique.lean` (local uniqueness) and
`SingularEndpoint/ConstantGraphonComparison/Expansions.lean`, and `SingularEndpoint/RankOneStationaryFamily/FamilyBuild.lean` assembles them into
`exists_kktFamily : Nonempty (KKTFamily d)` for `2 ≤ d`.

## Contents

* `exists_scalar_family` — the implicit function theorem applied to `Fsys`;
* `exists_scalar_family_components` — the same, split into `u_h`, `ℓ_h`, `γ_h`;
* `exists_scalar_family_kkt` — the three equations of `eq:three-value-kkt` along the
  family, for small `h ≠ 0`.
-/

namespace UpperTailOptimizers

open Filter Topology

variable {d : ℕ}

/-- **The coalescing family, as a solution of the desingularized system.**  This is
`analytic_implicit` applied to `Fsys`, with the three hypotheses supplied by
`analyticAt_Fsys`, `Fsys_base` and `exists_hasStrictFDerivAt_Fsys`. -/
theorem exists_scalar_family (hd : 2 ≤ d) :
    ∃ z : ℝ → ℝ × ℝ × ℝ,
      z 0 = zBase d ∧ (∀ᶠ h in 𝓝 (0 : ℝ), Fsys d (z h) h = 0) ∧ AnalyticAt ℝ z 0 := by
  obtain ⟨a, b, c, e, hb, hc, hL⟩ := exists_hasStrictFDerivAt_Fsys hd
  exact analytic_implicit (analyticAt_Fsys hd) (Fsys_base hd) (jac3 a b c e hb hc) hL

/-- The family split into its three components `u_h`, `ℓ_h`, `γ_h`, each analytic at `0` and
through the singular endpoint values `u_*`, `ℓ_*`, `γ_*`. -/
theorem exists_scalar_family_components (hd : 2 ≤ d) :
    ∃ u lv g : ℝ → ℝ,
      u 0 = uStar d ∧ lv 0 = ellStar d ∧ g 0 = gammaStar d ∧
      AnalyticAt ℝ u 0 ∧ AnalyticAt ℝ lv 0 ∧ AnalyticAt ℝ g 0 ∧
      (∀ᶠ h in 𝓝 (0 : ℝ),
        Esys1 d (lv h) (g h) (u h) h = 0 ∧ Esys2 d (g h) (u h) h = 0 ∧
          Esys3 d (g h) (u h) h = 0) := by
  obtain ⟨z, hz0, hzsol, hzan⟩ := exists_scalar_family hd
  refine ⟨fun h => (z h).1, fun h => (z h).2.1, fun h => (z h).2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (z 0).1 = uStar d
    rw [hz0]; rfl
  · show (z 0).2.1 = ellStar d
    rw [hz0]; rfl
  · show (z 0).2.2 = gammaStar d
    rw [hz0]; rfl
  · exact (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).analyticAt _ |>.fun_comp_of_eq hzan rfl
  · exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).analyticAt _ |>.fun_comp_of_eq hzan rfl
  · exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).analyticAt _ |>.fun_comp_of_eq hzan rfl
  · filter_upwards [hzsol] with h hh
    have := congrArg (fun w : ℝ × ℝ × ℝ => (w.1, w.2.1, w.2.2)) hh
    simp only [Fsys, Prod.mk.injEq] at this
    exact ⟨this.1, this.2.1, this.2.2⟩

/-- **The three rank-one KKT equations of `eq:three-value-kkt` along the family.**

For all sufficiently small `h ≠ 0` the three edge values `s_h², s_h t_h, t_h²` of the
two-valued factor are roots of `𝓛_h`, with `s_h = u_h - h` and `t_h = u_h + h`.  The
restriction `h ≠ 0` is exactly where `lell_three_eq_iff` applies; at `h = 0` the three roots
merge and the desingularized system is the correct statement instead. -/
theorem exists_scalar_family_kkt (hd : 2 ≤ d) :
    ∃ u lv g : ℝ → ℝ,
      u 0 = uStar d ∧ lv 0 = ellStar d ∧ g 0 = gammaStar d ∧
      AnalyticAt ℝ u 0 ∧ AnalyticAt ℝ lv 0 ∧ AnalyticAt ℝ g 0 ∧
      (∀ᶠ h in 𝓝 (0 : ℝ), h ≠ 0 →
        Lell d (lv h) (g h) ((u h - h) ^ 2) = 0 ∧
          Lell d (lv h) (g h) ((u h - h) * (u h + h)) = 0 ∧
          Lell d (lv h) (g h) ((u h + h) ^ 2) = 0) := by
  obtain ⟨u, lv, g, hu0, hlv0, hg0, hua, hlva, hga, hsol⟩ :=
    exists_scalar_family_components hd
  refine ⟨u, lv, g, hu0, hlv0, hg0, hua, hlva, hga, ?_⟩
  -- the admissibility side conditions hold near `h = 0` by continuity
  have hcont : ContinuousAt u 0 := hua.continuousAt
  have hs : Tendsto (fun h : ℝ => u h - h) (𝓝 0) (𝓝 (uStar d)) := by
    have := hcont.tendsto
    rw [hu0] at this
    simpa using this.sub (continuous_id.continuousAt (x := (0 : ℝ))).tendsto
  have ht : Tendsto (fun h : ℝ => u h + h) (𝓝 0) (𝓝 (uStar d)) := by
    have := hcont.tendsto
    rw [hu0] at this
    simpa using this.add (continuous_id.continuousAt (x := (0 : ℝ))).tendsto
  have hspos : ∀ᶠ h in 𝓝 (0 : ℝ), 0 < u h - h := hs.eventually_const_lt (uStar_pos hd)
  have htpos : ∀ᶠ h in 𝓝 (0 : ℝ), 0 < u h + h := ht.eventually_const_lt (uStar_pos hd)
  have hssq : ∀ᶠ h in 𝓝 (0 : ℝ), (u h - h) ^ 2 < 1 := by
    have : Tendsto (fun h : ℝ => (u h - h) ^ 2) (𝓝 0) (𝓝 (rStar d)) := by
      simpa [uStar_sq hd] using hs.pow 2
    exact this.eventually_lt_const (rStar_lt_one hd)
  have htsq : ∀ᶠ h in 𝓝 (0 : ℝ), (u h + h) ^ 2 < 1 := by
    have : Tendsto (fun h : ℝ => (u h + h) ^ 2) (𝓝 0) (𝓝 (rStar d)) := by
      simpa [uStar_sq hd] using ht.pow 2
    exact this.eventually_lt_const (rStar_lt_one hd)
  have hst : ∀ᶠ h in 𝓝 (0 : ℝ), (u h - h) * (u h + h) < 1 := by
    have : Tendsto (fun h : ℝ => (u h - h) * (u h + h)) (𝓝 0) (𝓝 (rStar d)) := by
      have := hs.mul ht
      rwa [show uStar d * uStar d = rStar d by rw [← uStar_sq hd]; ring] at this
    exact this.eventually_lt_const (rStar_lt_one hd)
  filter_upwards [hsol, hspos, htpos, hssq, htsq, hst] with h hsolh hsh hth hssqh htsqh hsth hne
  exact (lell_three_eq_iff hd hne hsh hth hssqh htsqh hsth).mpr hsolh

end UpperTailOptimizers
