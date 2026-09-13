import UpperTailOptimizers.KRRS.PsiCompare
import UpperTailOptimizers.KRRS.PsiUnique

/-!
# Construction of the Kenyon–Radin–Ren–Sadun cross density `ζ_d`

`KRRS/PsiUnique.lean` shows that `ψ_d(ε,·)` has *at most* one critical point off the diagonal.
This file produces it, and reads off every property Theorem 3.3 asserts.

## Existence

`KRRS/PsiCompare.lean` gives the sign of `W = ∂_zψ_d·𝒟²` on the two intervals where the ratio
`R_d` is monotone: `W(a,b) > 0` for `b ≤ r_*` and `W(a,b) < 0` for `r_* ≤ a`.  So for `ε < r_*`
one has `W(ε,r_*) > 0`, while `W(ε,z) → -∞` as `z → 1⁻` because `𝒩'_ε(z) = log((1-z)/z) - c`
diverges while `𝒟_ε(z)` stays positive; the intermediate value theorem then produces a zero in
`(r_*,1)`.  For `ε > r_*` the mirror argument uses `W(ε,z) → +∞` as `z → 0⁺`.

## The sign pattern

`W(ε,·)` vanishes in `(0,1)` exactly at `ε` and at `ζ_d(ε)`, so it has a constant sign on each
component of the complement, and the three signs are pinned down by the two divergences and by
the value at `r_*`.  The result is the clean trichotomy

  `W(ε,z) > 0 ↔ z < ζ_d(ε)`,  `W(ε,z) < 0 ↔ z > ζ_d(ε)`  (for `z ≠ ε`),

from which everything follows: `ψ_d(ε,·)` rises then falls, so `ζ_d(ε)` is the maximizer; and
since `W` is symmetric, `ε₁ < ε₂` gives `W(ζ_d(ε₁), ε₂) < 0`, i.e. `ζ_d(ε₂) < ζ_d(ε₁)`.

The comparison `ψ_d(ε,z) < R_d(ε) < ψ_d(ε,r_*)` of `KRRS/PsiCompare.lean` handles the values on
the near side of `ε`, which the monotonicity argument cannot reach across the singularity of
`ψ_d` at the diagonal.

## Contents

* `tendsto_Wr_atTop`, `tendsto_Wr_atBot` — the two divergences;
* `exists_crit` — the critical point exists off the exceptional density;
* `zetaFun`, `zetaFun_rStar`, `zetaFun_mem`, `zetaFun_eq_of_crit` — the selector;
* `Wr_pos_of_lt_zeta`, `Wr_neg_of_zeta_lt` — the trichotomy;
* `zetaFun_isMax`, `zetaFun_involutive`, `zetaFun_strictAntiOn` — Theorem 3.3.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

/-! ### Continuity of the ingredients -/

theorem continuous_S0 : Continuous S0 := by
  have h : S0 = fun u => Real.binEntropy u / 2 := by
    funext u; unfold S0; rw [shannonH_eq_binEntropy]
  rw [h]
  exact Real.binEntropy_continuous.div_const 2

theorem continuous_Nfun (ε : ℝ) : Continuous (fun z => Nfun ε z) := by
  unfold Nfun
  exact (((continuous_S0.sub continuous_const).sub
    ((continuous_id.sub continuous_const).const_mul (dS0 ε)))).const_mul 2

theorem continuous_Dfun (d : ℕ) (ε : ℝ) : Continuous (fun z => Dfun d ε z) := by
  unfold Dfun
  exact ((continuous_pow d).sub continuous_const).sub
    ((continuous_id.sub continuous_const).const_mul _)

theorem continuous_dD (d : ℕ) (ε : ℝ) : Continuous (fun z => dD d ε z) := by
  unfold dD
  exact ((continuous_pow (d - 1)).const_mul _).sub continuous_const

theorem continuousOn_Wr (d : ℕ) (ε : ℝ) {s t : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1)
    (ht : t ∈ Set.Ioo (0:ℝ) 1) : ContinuousOn (fun z => Wr d ε z) (Set.uIcc s t) := by
  intro x hx
  have h := uIcc_subset_Ioo hs.1 hs.2 ht.1 ht.2 hx
  exact ((hasDerivAt_Wr d ε (ne_of_gt h.1) (ne_of_lt h.2)).continuousAt).continuousWithinAt

/-! ### The two divergences of `𝒩'` -/

theorem tendsto_dN_atBot (ε : ℝ) : Tendsto (fun z => dN ε z) (𝓝[<] (1:ℝ)) atBot := by
  have h1 : Tendsto (fun z : ℝ => 1 - z) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun z : ℝ => 1 - z) (𝓝 (1:ℝ)) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_pos.mpr (Set.mem_Iio.mp hz)
  have hlog1 : Tendsto (fun z : ℝ => Real.log (1 - z)) (𝓝[<] (1:ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp h1
  have hc : Tendsto (fun z : ℝ => Real.log z) (𝓝[<] (1:ℝ)) (𝓝 0) := by
    have h : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have h2 := hc.neg.sub_const (Real.log (1 - ε) - Real.log ε)
  exact (hlog1.atBot_add h2).congr (fun z => by unfold dN; ring)

theorem tendsto_dN_atTop (ε : ℝ) : Tendsto (fun z => dN ε z) (𝓝[>] (0:ℝ)) atTop := by
  have hneg : Tendsto (fun z : ℝ => -Real.log z) (𝓝[>] (0:ℝ)) atTop := by
    simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hc : Tendsto (fun z : ℝ => Real.log (1 - z)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : ContinuousAt (fun z : ℝ => Real.log (1 - z)) 0 :=
      (continuous_const.sub continuous_id).continuousAt.log (by norm_num)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have h2 := hc.sub_const (Real.log (1 - ε) - Real.log ε)
  exact (hneg.atTop_add h2).congr (fun z => by unfold dN; ring)

/-! ### The two divergences of `W` -/

theorem tendsto_Wr_atBot {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun z => Wr d ε z) (𝓝[<] (1:ℝ)) atBot := by
  have hD : Tendsto (fun z => Dfun d ε z) (𝓝[<] (1:ℝ)) (𝓝 (Dfun d ε 1)) :=
    ((continuous_Dfun d ε).tendsto 1).mono_left nhdsWithin_le_nhds
  have hDpos : 0 < Dfun d ε 1 := Dfun_pos hd hε0 zero_le_one (ne_of_gt hε1)
  have h1 : Tendsto (fun z => dN ε z * Dfun d ε z) (𝓝[<] (1:ℝ)) atBot :=
    (tendsto_dN_atBot ε).atBot_mul_pos hDpos hD
  have h2 : Tendsto (fun z => -(Nfun ε z * dD d ε z)) (𝓝[<] (1:ℝ))
      (𝓝 (-(Nfun ε 1 * dD d ε 1))) :=
    ((((continuous_Nfun ε).mul (continuous_dD d ε)).neg).tendsto 1).mono_left nhdsWithin_le_nhds
  exact (h1.atBot_add h2).congr (fun z => by unfold Wr; ring)

theorem tendsto_Wr_atTop {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε0 : 0 < ε) :
    Tendsto (fun z => Wr d ε z) (𝓝[>] (0:ℝ)) atTop := by
  have hD : Tendsto (fun z => Dfun d ε z) (𝓝[>] (0:ℝ)) (𝓝 (Dfun d ε 0)) :=
    ((continuous_Dfun d ε).tendsto 0).mono_left nhdsWithin_le_nhds
  have hDpos : 0 < Dfun d ε 0 := Dfun_pos hd hε0 le_rfl (ne_of_lt hε0)
  have h1 : Tendsto (fun z => dN ε z * Dfun d ε z) (𝓝[>] (0:ℝ)) atTop :=
    (tendsto_dN_atTop ε).atTop_mul_pos hDpos hD
  have h2 : Tendsto (fun z => -(Nfun ε z * dD d ε z)) (𝓝[>] (0:ℝ))
      (𝓝 (-(Nfun ε 0 * dD d ε 0))) :=
    ((((continuous_Nfun ε).mul (continuous_dD d ε)).neg).tendsto 0).mono_left nhdsWithin_le_nhds
  exact (h1.atTop_add h2).congr (fun z => by unfold Wr; ring)

theorem exists_Wr_neg_near_one {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hu : u < 1) : ∃ z, u < z ∧ z < 1 ∧ Wr d ε z < 0 := by
  have h := (tendsto_Wr_atBot hd hε0 hε1).eventually (eventually_lt_atBot (0:ℝ))
  have h2 : ∀ᶠ x in 𝓝[<] (1:ℝ), x ∈ Set.Ioo u 1 :=
    Filter.eventually_of_mem (Ioo_mem_nhdsLT hu) (fun x hx => hx)
  obtain ⟨z, hzW, hzmem⟩ := (h.and h2).exists
  exact ⟨z, hzmem.1, hzmem.2, hzW⟩

theorem exists_Wr_pos_near_zero {d : ℕ} (hd : 2 ≤ d) {ε u : ℝ} (hε0 : 0 < ε) (hu : 0 < u) :
    ∃ z, 0 < z ∧ z < u ∧ 0 < Wr d ε z := by
  have h := (tendsto_Wr_atTop hd hε0).eventually (eventually_gt_atTop (0:ℝ))
  have h2 : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioo (0:ℝ) u :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT hu) (fun x hx => hx)
  obtain ⟨z, hzW, hzmem⟩ := (h.and h2).exists
  exact ⟨z, hzmem.1, hzmem.2, hzW⟩

/-! ### Existence of the off-diagonal critical point -/

/-- **The critical point exists.**  Away from the exceptional density, `W(ε,·)` has the sign of
the monotone side at `r_*` and the opposite sign near the far endpoint, so it vanishes in
between. -/
theorem exists_crit {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hεr : ε ≠ rStar d) : ∃ z, z ∈ Set.Ioo (0:ℝ) 1 ∧ z ≠ ε ∧ Wr d ε z = 0 := by
  have hr0 : 0 < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  rcases lt_or_gt_of_ne hεr with hlt | hgt
  · -- `ε < r_*`: `W(ε,r_*) > 0` and `W(ε,·) < 0` near `1`
    obtain ⟨z₁, hz₁r, hz₁1, hz₁W⟩ := exists_Wr_neg_near_one hd hε0 hε1 hr1
    have hpos : 0 < Wr d ε (rStar d) := Wr_pos_of_le_rStar hd hε0 hlt le_rfl
    have hcont : ContinuousOn (fun z => Wr d ε z) (Set.Icc (rStar d) z₁) := by
      have h := continuousOn_Wr d ε (s := rStar d) (t := z₁) ⟨hr0, hr1⟩ ⟨lt_trans hr0 hz₁r, hz₁1⟩
      rwa [Set.uIcc_of_le hz₁r.le] at h
    have hmem : (0:ℝ) ∈ Set.Icc (Wr d ε z₁) (Wr d ε (rStar d)) := ⟨hz₁W.le, hpos.le⟩
    obtain ⟨z, hzmem, hzW⟩ := intermediate_value_Icc' hz₁r.le hcont hmem
    exact ⟨z, ⟨lt_of_lt_of_le hr0 hzmem.1, lt_of_le_of_lt hzmem.2 hz₁1⟩,
      ne_of_gt (lt_of_lt_of_le hlt hzmem.1), hzW⟩
  · -- `ε > r_*`: `W(ε,r_*) < 0` and `W(ε,·) > 0` near `0`
    obtain ⟨z₀, hz₀0, hz₀r, hz₀W⟩ := exists_Wr_pos_near_zero hd hε0 hr0
    have hneg : Wr d ε (rStar d) < 0 := by
      have h := Wr_neg_of_rStar_le hd (le_refl (rStar d)) hgt hε1
      rwa [Wr_swap] at h
    have hcont : ContinuousOn (fun z => Wr d ε z) (Set.Icc z₀ (rStar d)) := by
      have h := continuousOn_Wr d ε (s := z₀) (t := rStar d) ⟨hz₀0, lt_trans hz₀r hr1⟩ ⟨hr0, hr1⟩
      rwa [Set.uIcc_of_le hz₀r.le] at h
    have hmem : (0:ℝ) ∈ Set.Icc (Wr d ε (rStar d)) (Wr d ε z₀) := ⟨hneg.le, hz₀W.le⟩
    obtain ⟨z, hzmem, hzW⟩ := intermediate_value_Icc' hz₀r.le hcont hmem
    exact ⟨z, ⟨lt_of_lt_of_le hz₀0 hzmem.1, lt_of_le_of_lt hzmem.2 hr1⟩,
      ne_of_lt (lt_of_le_of_lt hzmem.2 hgt), hzW⟩

/-! ### The selector `ζ_d` -/

open Classical in
/-- **The Kenyon–Radin–Ren–Sadun cross density `ζ_d`**, selected as the off-diagonal critical
point of `ψ_d(ε,·)` — which exists (`exists_crit`) and is unique (`crit_unique`).  At the
exceptional density there is none (`no_crit_rStar`) and the definition falls back to `ε`,
which is the value Theorem 3.3's fixed-point clause demands. -/
noncomputable def zetaFun (d : ℕ) (ε : ℝ) : ℝ :=
  if h : ∃ z, z ∈ Set.Ioo (0:ℝ) 1 ∧ z ≠ ε ∧ Wr d ε z = 0 then h.choose else ε

theorem zetaFun_spec {d : ℕ} {ε : ℝ} (h : ∃ z, z ∈ Set.Ioo (0:ℝ) 1 ∧ z ≠ ε ∧ Wr d ε z = 0) :
    zetaFun d ε ∈ Set.Ioo (0:ℝ) 1 ∧ zetaFun d ε ≠ ε ∧ Wr d ε (zetaFun d ε) = 0 := by
  unfold zetaFun
  rw [dif_pos h]
  exact h.choose_spec

theorem zetaFun_crit {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hεr : ε ≠ rStar d) :
    zetaFun d ε ∈ Set.Ioo (0:ℝ) 1 ∧ zetaFun d ε ≠ ε ∧ Wr d ε (zetaFun d ε) = 0 :=
  zetaFun_spec (exists_crit hd hε0 hε1 hεr)

/-- **`ζ_d` fixes the exceptional density** — Step 1 of Theorem 3.3. -/
theorem zetaFun_rStar {d : ℕ} (hd : 2 ≤ d) : zetaFun d (rStar d) = rStar d := by
  unfold zetaFun
  rw [dif_neg]
  rintro ⟨z, hz, hzne, hzW⟩
  exact no_crit_rStar hd hz.1 hz.2 hzne hzW

theorem zetaFun_mem {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1) :
    zetaFun d ε ∈ Set.Ioo (0:ℝ) 1 := by
  by_cases hεr : ε = rStar d
  · rw [hεr, zetaFun_rStar hd]
    exact ⟨rStar_pos hd, rStar_lt_one hd⟩
  · exact (zetaFun_crit hd hε.1 hε.2 hεr).1

/-- **Uniqueness**: any off-diagonal critical point *is* `ζ_d(ε)`. -/
theorem zetaFun_eq_of_crit {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    (hz : z ∈ Set.Ioo (0:ℝ) 1) (hne : z ≠ ε) (hcrit : Wr d ε z = 0) : z = zetaFun d ε := by
  by_cases hεr : ε = rStar d
  · rw [hεr] at hcrit hne
    exact absurd hcrit (no_crit_rStar hd hz.1 hz.2 hne)
  · obtain ⟨hym, hyne, hyW⟩ := zetaFun_crit hd hε.1 hε.2 hεr
    exact crit_unique hd hε.1 hε.2 hz.1 hz.2 hym.1 hym.2 hne hyne hcrit hyW

theorem zetaFun_ne_self {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    (hεr : ε ≠ rStar d) : zetaFun d ε ≠ ε := (zetaFun_crit hd hε.1 hε.2 hεr).2.1

/-! ### The sign pattern of `W(ε,·)` -/

private theorem uIcc_subset_Ioo' {a b s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    Set.uIcc s t ⊆ Set.Ioo a b := fun _ hx =>
  ⟨lt_of_lt_of_le (lt_min hs.1 ht.1) hx.1, lt_of_le_of_lt hx.2 (max_lt hs.2 ht.2)⟩

private theorem Wr_pos_transfer {d : ℕ} {ε : ℝ} {s t : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1)
    (ht : t ∈ Set.Ioo (0:ℝ) 1) (hnz : ∀ x ∈ Set.uIcc s t, Wr d ε x ≠ 0)
    (hpos : 0 < Wr d ε s) : 0 < Wr d ε t := by
  by_contra hcon
  push Not at hcon
  have htneg : Wr d ε t < 0 := lt_of_le_of_ne hcon (hnz t Set.right_mem_uIcc)
  have hmem : (0:ℝ) ∈ Set.uIcc (Wr d ε s) (Wr d ε t) :=
    Set.mem_uIcc.mpr (Or.inr ⟨htneg.le, hpos.le⟩)
  obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc (continuousOn_Wr d ε hs ht) hmem
  exact hnz c hc hc0

private theorem Wr_neg_transfer {d : ℕ} {ε : ℝ} {s t : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1)
    (ht : t ∈ Set.Ioo (0:ℝ) 1) (hnz : ∀ x ∈ Set.uIcc s t, Wr d ε x ≠ 0)
    (hneg : Wr d ε s < 0) : Wr d ε t < 0 := by
  by_contra hcon
  push Not at hcon
  have htpos : 0 < Wr d ε t := lt_of_le_of_ne hcon (Ne.symm (hnz t Set.right_mem_uIcc))
  have hmem : (0:ℝ) ∈ Set.uIcc (Wr d ε s) (Wr d ε t) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hneg.le, htpos.le⟩)
  obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc (continuousOn_Wr d ε hs ht) hmem
  exact hnz c hc hc0

theorem Wr_self (d : ℕ) (ε : ℝ) : Wr d ε ε = 0 := by
  unfold Wr Nfun Dfun dN dD; ring

theorem zetaFun_Wr_eq_zero {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1) :
    Wr d ε (zetaFun d ε) = 0 := by
  by_cases hεr : ε = rStar d
  · rw [hεr, zetaFun_rStar hd, Wr_self]
  · exact (zetaFun_crit hd hε.1 hε.2 hεr).2.2

/-- The zeros of `W(ε,·)` in `(0,1)` are exactly `ε` and `ζ_d(ε)`. -/
theorem Wr_ne_zero {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1) :
    ∀ x ∈ Set.Ioo (0:ℝ) 1, x ≠ ε → x ≠ zetaFun d ε → Wr d ε x ≠ 0 :=
  fun _ hx hxe hxy hc => hxy (zetaFun_eq_of_crit hd hε hx hxe hc)

/-- **`W(ε,z) > 0` strictly below `ζ_d(ε)`.** -/
theorem Wr_pos_of_lt_zeta {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    (hz : z ∈ Set.Ioo (0:ℝ) 1) (hne : z ≠ ε) (hlt : z < zetaFun d ε) : 0 < Wr d ε z := by
  have hy : zetaFun d ε ∈ Set.Ioo (0:ℝ) 1 := zetaFun_mem hd hε
  have hzeros := Wr_ne_zero hd hε
  rcases lt_or_gt_of_ne hne with hzε | hzε
  · -- `z` lies below both `ε` and `ζ_d(ε)`: transfer from a point near `0`
    obtain ⟨p, hp0, hpz, hpW⟩ := exists_Wr_pos_near_zero hd hε.1 hz.1
    have hsub : Set.uIcc p z ⊆ Set.Ioo (0:ℝ) (min ε (zetaFun d ε)) :=
      uIcc_subset_Ioo' ⟨hp0, lt_min (lt_trans hpz hzε) (lt_trans hpz hlt)⟩
        ⟨hz.1, lt_min hzε hlt⟩
    refine Wr_pos_transfer ⟨hp0, lt_trans (lt_trans hpz hzε) hε.2⟩ hz (fun x hx => ?_) hpW
    have hx' := hsub hx
    have hxe : x < ε := lt_of_lt_of_le hx'.2 (min_le_left _ _)
    have hxy : x < zetaFun d ε := lt_of_lt_of_le hx'.2 (min_le_right _ _)
    exact hzeros x ⟨hx'.1, lt_trans hxe hε.2⟩ (ne_of_lt hxe) (ne_of_lt hxy)
  · -- `ε < z < ζ_d(ε)`: transfer from `r_*`, which lies strictly between
    have hyne : zetaFun d ε ≠ ε := ne_of_gt (lt_trans hzε hlt)
    have hside := crit_side hd hε.1 hε.2 hy.1 hy.2 hyne (zetaFun_Wr_eq_zero hd hε)
    have hεr : ε < rStar d ∧ rStar d < zetaFun d ε := by
      rcases hside with h | h
      · exact h
      · exact absurd (lt_trans h.1 h.2) (not_lt.mpr (lt_trans hzε hlt).le)
    have hrmem : rStar d ∈ Set.Ioo ε (zetaFun d ε) := ⟨hεr.1, hεr.2⟩
    have hrpos : 0 < Wr d ε (rStar d) := Wr_pos_of_le_rStar hd hε.1 hεr.1 le_rfl
    refine Wr_pos_transfer (s := rStar d) (t := z) ⟨rStar_pos hd, rStar_lt_one hd⟩ hz
      (fun x hx => ?_) hrpos
    have hx' : x ∈ Set.Ioo ε (zetaFun d ε) := uIcc_subset_Ioo' hrmem ⟨hzε, hlt⟩ hx
    exact hzeros x ⟨lt_trans hε.1 hx'.1, lt_trans hx'.2 hy.2⟩ (ne_of_gt hx'.1) (ne_of_lt hx'.2)

/-- **`W(ε,z) < 0` strictly above `ζ_d(ε)`.** -/
theorem Wr_neg_of_zeta_lt {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    (hz : z ∈ Set.Ioo (0:ℝ) 1) (hne : z ≠ ε) (hgt : zetaFun d ε < z) : Wr d ε z < 0 := by
  have hy : zetaFun d ε ∈ Set.Ioo (0:ℝ) 1 := zetaFun_mem hd hε
  have hzeros := Wr_ne_zero hd hε
  rcases lt_or_gt_of_ne hne with hzε | hzε
  · -- `ζ_d(ε) < z < ε`: transfer from `r_*`, which lies strictly between
    have hyne : zetaFun d ε ≠ ε := ne_of_lt (lt_trans hgt hzε)
    have hside := crit_side hd hε.1 hε.2 hy.1 hy.2 hyne (zetaFun_Wr_eq_zero hd hε)
    have hεr : zetaFun d ε < rStar d ∧ rStar d < ε := by
      rcases hside with h | h
      · exact absurd (lt_trans h.1 h.2) (not_lt.mpr (lt_trans hgt hzε).le)
      · exact h
    have hrmem : rStar d ∈ Set.Ioo (zetaFun d ε) ε := ⟨hεr.1, hεr.2⟩
    have hrneg : Wr d ε (rStar d) < 0 := by
      have h := Wr_neg_of_rStar_le hd (le_refl (rStar d)) hεr.2 hε.2
      rwa [Wr_swap] at h
    refine Wr_neg_transfer (s := rStar d) (t := z) ⟨rStar_pos hd, rStar_lt_one hd⟩ hz
      (fun x hx => ?_) hrneg
    have hx' : x ∈ Set.Ioo (zetaFun d ε) ε := uIcc_subset_Ioo' hrmem ⟨hgt, hzε⟩ hx
    exact hzeros x ⟨lt_trans hy.1 hx'.1, lt_trans hx'.2 hε.2⟩ (ne_of_lt hx'.2) (ne_of_gt hx'.1)
  · -- `z` lies above both: transfer from a point near `1`
    obtain ⟨p, hzp, hp1, hpW⟩ := exists_Wr_neg_near_one hd hε.1 hε.2 hz.2
    have hsub : Set.uIcc p z ⊆ Set.Ioo (max ε (zetaFun d ε)) 1 :=
      uIcc_subset_Ioo' ⟨max_lt (lt_trans hzε hzp) (lt_trans hgt hzp), hp1⟩
        ⟨max_lt hzε hgt, hz.2⟩
    refine Wr_neg_transfer (s := p) (t := z) ⟨lt_trans hz.1 hzp, hp1⟩ hz (fun x hx => ?_) hpW
    have hx' := hsub hx
    have hxe : ε < x := lt_of_le_of_lt (le_max_left _ _) hx'.1
    have hxy : zetaFun d ε < x := lt_of_le_of_lt (le_max_right _ _) hx'.1
    exact hzeros x ⟨lt_trans hε.1 hxe, hx'.2⟩ (ne_of_gt hxe) (ne_of_gt hxy)

/-! ### `ψ_d(ε,·)` rises to `ζ_d(ε)` and falls after it -/

theorem hasDerivAt_psiD {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hz0 : 0 < z) (hz1 : z < 1)
    (hne : z ≠ ε) : HasDerivAt (fun w => psiD d ε w) (Wr d ε z / Dfun d ε z ^ 2) z := by
  have hD : Dfun d ε z ≠ 0 := ne_of_gt (Dfun_pos hd hε0 hz0.le hne)
  have h := (hasDerivAt_Nfun ε (ne_of_gt hz0) (ne_of_lt hz1)).div (hasDerivAt_Dfun d ε z) hD
  have hfun : (fun w => psiD d ε w) = fun w => Nfun ε w / Dfun d ε w := rfl
  have hval : Wr d ε z / Dfun d ε z ^ 2
      = (dN ε z * Dfun d ε z - Nfun ε z * dD d ε z) / Dfun d ε z ^ 2 := rfl
  rw [hfun, hval]
  exact h

theorem psiD_strictMonoOn {d : ℕ} (hd : 2 ≤ d) {ε a b : ℝ} (hε0 : 0 < ε) (ha0 : 0 < a)
    (hb1 : b < 1) (hne : ∀ x ∈ Set.Icc a b, x ≠ ε) (hpos : ∀ x ∈ Set.Ioo a b, 0 < Wr d ε x) :
    StrictMonoOn (fun w => psiD d ε w) (Set.Icc a b) := by
  have hmem : ∀ x ∈ Set.Icc a b, 0 < x ∧ x < 1 := fun x hx =>
    ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun w => psiD d ε w) (Wr d ε x / Dfun d ε x ^ 2) x := fun x hx =>
    hasDerivAt_psiD hd hε0 (hmem x hx).1 (hmem x hx).2 (hne x hx)
  refine strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
  rw [interior_Icc] at hx
  have hxmem : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
  rw [(hderiv x hxmem).deriv]
  have hD : 0 < Dfun d ε x := Dfun_pos hd hε0 (hmem x hxmem).1.le (hne x hxmem)
  exact div_pos (hpos x hx) (by positivity)

theorem psiD_strictAntiOn {d : ℕ} (hd : 2 ≤ d) {ε a b : ℝ} (hε0 : 0 < ε) (ha0 : 0 < a)
    (hb1 : b < 1) (hne : ∀ x ∈ Set.Icc a b, x ≠ ε) (hneg : ∀ x ∈ Set.Ioo a b, Wr d ε x < 0) :
    StrictAntiOn (fun w => psiD d ε w) (Set.Icc a b) := by
  have hmem : ∀ x ∈ Set.Icc a b, 0 < x ∧ x < 1 := fun x hx =>
    ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun w => psiD d ε w) (Wr d ε x / Dfun d ε x ^ 2) x := fun x hx =>
    hasDerivAt_psiD hd hε0 (hmem x hx).1 (hmem x hx).2 (hne x hx)
  refine strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
  rw [interior_Icc] at hx
  have hxmem : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
  rw [(hderiv x hxmem).deriv]
  have hD : 0 < Dfun d ε x := Dfun_pos hd hε0 (hmem x hxmem).1.le (hne x hxmem)
  exact div_neg_of_neg_of_pos (hneg x hx) (by positivity)

/-! ### `ζ_d(ε)` is the maximizer -/

/-- The far side of `ε`: `ψ_d(ε,·)` rises to `ζ_d(ε)` and falls after it, so `ζ_d(ε)` beats
every point that `ε` does not separate it from. -/
private theorem psiD_le_of_side {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    (hz : z ∈ Set.Ioo (0:ℝ) 1) (hsep : ∀ x ∈ Set.uIcc z (zetaFun d ε), x ≠ ε) :
    psiD d ε z ≤ psiD d ε (zetaFun d ε) := by
  have hy : zetaFun d ε ∈ Set.Ioo (0:ℝ) 1 := zetaFun_mem hd hε
  rcases lt_trichotomy z (zetaFun d ε) with hlt | heq | hgt
  · have hIcc : Set.uIcc z (zetaFun d ε) = Set.Icc z (zetaFun d ε) := Set.uIcc_of_le hlt.le
    rw [hIcc] at hsep
    have hmono := psiD_strictMonoOn hd hε.1 hz.1 hy.2 hsep (fun x hx =>
      Wr_pos_of_lt_zeta hd hε ⟨lt_trans hz.1 hx.1, lt_trans hx.2 hy.2⟩
        (hsep x ⟨hx.1.le, hx.2.le⟩) hx.2)
    exact (hmono (Set.left_mem_Icc.mpr hlt.le) (Set.right_mem_Icc.mpr hlt.le) hlt).le
  · rw [heq]
  · have hIcc : Set.uIcc z (zetaFun d ε) = Set.Icc (zetaFun d ε) z := Set.uIcc_of_ge hgt.le
    rw [hIcc] at hsep
    have hanti := psiD_strictAntiOn hd hε.1 hy.1 hz.2 hsep (fun x hx =>
      Wr_neg_of_zeta_lt hd hε ⟨lt_trans hy.1 hx.1, lt_trans hx.2 hz.2⟩
        (hsep x ⟨hx.1.le, hx.2.le⟩) hx.1)
    exact (hanti (Set.left_mem_Icc.mpr hgt.le) (Set.right_mem_Icc.mpr hgt.le) hgt).le

/-- **`ζ_d(ε)` maximises `ψ_d(ε,·)`.**  On the far side of `ε` this is the sign pattern of `W`;
on the near side it is the comparison `ψ_d(ε,z) < R_d(ε) < ψ_d(ε,r_*)` of
`KRRS/PsiCompare.lean`, since `R_d` is monotone between `ε` and `r_*`. -/
theorem zetaFun_isMax {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1) :
    ∀ z ∈ Set.Ioo (0:ℝ) 1, z ≠ ε → psiD d ε z ≤ psiD d ε (zetaFun d ε) := by
  have hr0 : 0 < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  by_cases hεr : ε = rStar d
  · -- at the exceptional density `ζ_d` is the identity and every off-diagonal value is negative
    intro z hz hzne
    rw [hεr, zetaFun_rStar hd, ← hεr]
    have hdiag : psiD d ε ε = 0 := by
      have hN : Nfun ε ε = 0 := by unfold Nfun; ring
      unfold psiD; rw [hN, zero_div]
    rw [hdiag]
    exact (psiD_neg hd hε.1 hε.2 hz.1 hz.2 hzne).le
  · have hy : zetaFun d ε ∈ Set.Ioo (0:ℝ) 1 := zetaFun_mem hd hε
    have hyne : zetaFun d ε ≠ ε := zetaFun_ne_self hd hε hεr
    have hside := crit_side hd hε.1 hε.2 hy.1 hy.2 hyne (zetaFun_Wr_eq_zero hd hε)
    rcases hside with ⟨hεlt, hrlt⟩ | ⟨hrlt, hεgt⟩
    · -- `ε < r_* < ζ_d(ε)`
      have hfar : ∀ z ∈ Set.Ioo (0:ℝ) 1, ε < z → psiD d ε z ≤ psiD d ε (zetaFun d ε) := by
        intro z hz hzε
        refine psiD_le_of_side hd hε hz (fun x hx => ?_)
        have hx' : x ∈ Set.Ioo ε 1 :=
          uIcc_subset_Ioo' (a := ε) (b := 1) ⟨hzε, hz.2⟩ ⟨lt_trans hεlt hrlt, hy.2⟩ hx
        exact ne_of_gt hx'.1
      intro z hz hzne
      rcases lt_or_gt_of_ne hzne with hlt | hgt
      · have h1 : psiD d ε z < Rfun d ε := by
          refine psiD_lt_of_Rfun_lt hd hε.1 hε.2 hz.1 hz.2 hzne (fun s hs => ?_)
          rw [min_eq_right hlt.le, max_eq_left hlt.le] at hs
          exact Rfun_strictMonoOn hd ⟨lt_trans hz.1 hs.1, le_trans hs.2.le hεlt.le⟩
            ⟨hε.1, hεlt.le⟩ hs.2
        have h2 : Rfun d ε < psiD d ε (rStar d) := by
          refine lt_psiD_of_lt_Rfun hd hε.1 hε.2 hr0 hr1 (ne_of_gt hεlt) (fun s hs => ?_)
          rw [min_eq_left hεlt.le, max_eq_right hεlt.le] at hs
          exact Rfun_strictMonoOn hd ⟨hε.1, hεlt.le⟩ ⟨lt_trans hε.1 hs.1, hs.2.le⟩ hs.1
        have h3 := hfar (rStar d) ⟨hr0, hr1⟩ hεlt
        linarith
      · exact hfar z hz hgt
    · -- `ζ_d(ε) < r_* < ε`
      have hfar : ∀ z ∈ Set.Ioo (0:ℝ) 1, z < ε → psiD d ε z ≤ psiD d ε (zetaFun d ε) := by
        intro z hz hzε
        refine psiD_le_of_side hd hε hz (fun x hx => ?_)
        have hx' : x ∈ Set.Ioo 0 ε :=
          uIcc_subset_Ioo' (a := 0) (b := ε) ⟨hz.1, hzε⟩ ⟨hy.1, lt_trans hrlt hεgt⟩ hx
        exact ne_of_lt hx'.2
      intro z hz hzne
      rcases lt_or_gt_of_ne hzne with hlt | hgt
      · exact hfar z hz hlt
      · have h1 : psiD d ε z < Rfun d ε := by
          refine psiD_lt_of_Rfun_lt hd hε.1 hε.2 hz.1 hz.2 hzne (fun s hs => ?_)
          rw [min_eq_left hgt.le, max_eq_right hgt.le] at hs
          exact Rfun_strictAntiOn hd ⟨hεgt.le, hε.2⟩ ⟨le_trans hεgt.le hs.1.le, hs.2.trans hz.2⟩
            hs.1
        have h2 : Rfun d ε < psiD d ε (rStar d) := by
          refine lt_psiD_of_lt_Rfun hd hε.1 hε.2 hr0 hr1 (ne_of_lt hεgt) (fun s hs => ?_)
          rw [min_eq_right hεgt.le, max_eq_left hεgt.le] at hs
          exact Rfun_strictAntiOn hd ⟨hs.1.le, lt_trans hs.2 hε.2⟩ ⟨hεgt.le, hε.2⟩ hs.2
        have h3 := hfar (rStar d) ⟨hr0, hr1⟩ hεgt
        linarith

/-! ### `ζ_d` is a strictly decreasing involution -/

/-- **`ζ_d` is an involution** — Step 3 of Theorem 3.3, from the symmetry of `W`. -/
theorem zetaFun_involutive {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1) :
    zetaFun d (zetaFun d ε) = ε := by
  by_cases hεr : ε = rStar d
  · rw [hεr, zetaFun_rStar hd, zetaFun_rStar hd]
  · have hy : zetaFun d ε ∈ Set.Ioo (0:ℝ) 1 := zetaFun_mem hd hε
    have hyne : zetaFun d ε ≠ ε := zetaFun_ne_self hd hε hεr
    have hW : Wr d (zetaFun d ε) ε = 0 := Wr_eq_zero_swap (zetaFun_Wr_eq_zero hd hε)
    exact (zetaFun_eq_of_crit hd hy hε (Ne.symm hyne) hW).symm

/-- **`ζ_d` is strictly decreasing** — the remaining clause of Theorem 3.3.

If `ε₁ < ε₂` and `y₁ := ζ_d(ε₁)`, then `ζ_d(y₁) = ε₁ < ε₂`, so `W(y₁, ε₂) < 0`; symmetry of `W`
turns that into `W(ε₂, y₁) < 0`, which puts `y₁` strictly above `ζ_d(ε₂)`. -/
theorem zetaFun_strictAntiOn {d : ℕ} (hd : 2 ≤ d) :
    StrictAntiOn (zetaFun d) (Set.Ioo (0:ℝ) 1) := by
  intro ε₁ h₁ ε₂ h₂ hlt
  have hy₁ : zetaFun d ε₁ ∈ Set.Ioo (0:ℝ) 1 := zetaFun_mem hd h₁
  have hinv : zetaFun d (zetaFun d ε₁) = ε₁ := zetaFun_involutive hd h₁
  by_cases heq : ε₂ = zetaFun d ε₁
  · rw [heq, hinv]; rw [heq] at hlt; exact hlt
  · have hW : Wr d (zetaFun d ε₁) ε₂ < 0 := by
      refine Wr_neg_of_zeta_lt hd hy₁ h₂ heq ?_
      rw [hinv]; exact hlt
    have hW' : Wr d ε₂ (zetaFun d ε₁) < 0 := by rw [Wr_swap]; exact hW
    have hle : zetaFun d ε₂ ≤ zetaFun d ε₁ := by
      by_contra hcon
      push Not at hcon
      have := Wr_pos_of_lt_zeta hd h₂ hy₁ (Ne.symm heq) hcon
      linarith
    refine lt_of_le_of_ne hle (fun hcon => ?_)
    have : ε₂ = ε₁ := by
      have h := congrArg (zetaFun d) hcon
      rwa [zetaFun_involutive hd h₂, hinv] at h
    exact absurd this (ne_of_gt hlt)

end UpperTailOptimizers
