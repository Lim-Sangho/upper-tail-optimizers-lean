import UpperTailOptimizers.LZBoundary.PhiConvex
import UpperTailOptimizers.Preliminaries.Graphons.Basic

/-!
# Second derivative and convex/concave structure of `φ_{p,d}` (`lem:convexity-defect` of
`paper/paper.tex`)

For `p < p_*` the convexity defect `h_{p,d}` is negative at `r_*` and tends to
`+∞` at both ends of `(0,1)`; being strictly monotone on each side of `r_*`, it
has two zeros `u₋ < r_* < u₊`.  Since the sign of `φ_{p,d}''` is the sign of
`h_{p,d}`, this gives the convex–concave–convex structure: `φ_{p,d}` is strictly
convex on `[0,u₋^d]` and on `[u₊^d,1]` and strictly concave on `[u₋^d,u₊^d]`.

Together with `LZBoundary/Phi.lean` (clauses (a)–(c) at the level of `h_{p,d}`) and
`LZBoundary/PhiConvex.lean` (the `p_*` threshold), this file completes `lem:convexity-defect`
(`lem:convexity-defect`) and packages it as `convexity_defect`.  The two zeros are
produced **existentially**; see that theorem's docstring for why they are not named as
functions of `p`.  The boundary-slope limits and `phi_continuousOn_Icc` recorded here feed
`lem:contact-points` in `LZBoundary/Existence.lean`.

## Contents

* `hpd_tendsto_atTop_zero`, `hpd_tendsto_atTop_one` — the two boundary blow-ups of `h_{p,d}`.
* `hpd_left_zero`, `hpd_right_zero` — `lem:convexity-defect`(f): for `p < p_*`, the zeros `u₋ ∈ (0,r_*)`
  and `u₊ ∈ (r_*,1)`, each bundled with positivity of `h_{p,d}` on the outer side.
* `phi''`, `hasDerivAt_phi''`, `phi''_pos_iff`, `phi''_neg_iff` — `lem:convexity-defect`(d): the explicit
  formula `φ_{p,d}''(x) = h_{p,d}(z)/(d² z^{2d-1})` and the equality of signs.
* `Jp'_tendsto_atBot`, `Jp'_tendsto_atTop_one`, `phi'_tendsto_atBot`, `phi'_tendsto_atTop`,
  `phi_continuousOn_Icc` — boundary behaviour of `J_p'`, `φ_{p,d}'` and continuity on `[0,1]`.
* `hpd_strictAntiOn_Ioc`, `hpd_strictMonoOn_Ico`, `hpd_rStar_lt_of_ne` — `lem:convexity-defect`(c): the
  endpoint-inclusive monotonicity and the unique minimum at `r_*`.
* `hpd_nonneg_of_pStar_le`, `convexOn_phi_of_pStar_le` — `lem:convexity-defect`(e): above the threshold.
* `strictConvexOn_phi_left`, `strictConvexOn_phi_right` — strict convexity of `φ_{p,d}` on
  `[0,c]` / `[c,1]` from the sign of `φ_{p,d}''` there.
* `hpd_neg_of_between_zeros`, `hpd_eq_zero_iff_of_zeros` — `lem:convexity-defect`(f): negativity between
  the two zeros, and that they are the only ones.
* `strictConvexOn_phi_lower`, `strictConcaveOn_phi_middle`, `strictConvexOn_phi_upper` —
  `lem:convexity-defect`(g): the three curvature intervals `[0,u₋^d]`, `[u₋^d,u₊^d]`, `[u₊^d,1]`.
* `convexity_defect` — `lem:convexity-defect` as a single declaration.
-/

namespace UpperTailOptimizers

open Real Filter Topology

section
variable {d : ℕ}

/-- `Set.Ioo 0 1` is a neighbourhood of `0` within `(0,∞)`. -/
private theorem Ioo_mem_nhdsWithin_zero : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) :=
  mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, by norm_num, by
    rintro x ⟨hx1, hx0⟩; exact ⟨hx0, hx1⟩⟩

/-- `Set.Ioo 0 1` is a neighbourhood of `1` within `(-∞,1)`. -/
private theorem Ioo_mem_nhdsWithin_one : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) :=
  mem_nhdsWithin.mpr ⟨Set.Ioi 0, isOpen_Ioi, by norm_num, by
    rintro x ⟨hx0, hx1⟩; exact ⟨hx0, hx1⟩⟩

/-- As `u → 0⁺`, `h_{p,d}(u) → +∞`. -/
theorem hpd_tendsto_atTop_zero (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (hpd p d) (𝓝[>] (0:ℝ)) atTop := by
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by have := one_lt_d hd; linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  have heq : (hpd p d) =ᶠ[𝓝[>] (0:ℝ)] (fun u => -(((d:ℝ) - 1) * Jp' p u) + (1 - u)⁻¹) := by
    filter_upwards [Ioo_mem_nhdsWithin_zero] with u hu
    rw [hpd_eq hu.1 hu.2]; ring
  rw [tendsto_congr' heq]
  -- `(1-u)⁻¹ → 1`
  have h1 : Tendsto (fun u : ℝ => (1 - u)⁻¹) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hca : ContinuousAt (fun u : ℝ => (1 - u)⁻¹) 0 :=
      ContinuousAt.inv₀ (by fun_prop) (by norm_num)
    have := hca.tendsto
    simp only [sub_zero, inv_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- `J_p'(u) = log(u(1-p)/((1-u)p)) → -∞`
  have hAca : ContinuousAt (fun u : ℝ => u * (1 - p) / ((1 - u) * p)) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hpne)
  have hAt0 : Tendsto (fun u : ℝ => u * (1 - p) / ((1 - u) * p)) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa using hAca.tendsto
  have hA : Tendsto (fun u : ℝ => u * (1 - p) / ((1 - u) * p)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hAt0.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsWithin_zero] with u hu
    have hu0 : (0:ℝ) < u := hu.1
    have h1u : (0:ℝ) < 1 - u := by linarith [hu.2]
    have hp1' : (0:ℝ) < 1 - p := by linarith
    exact Set.mem_Ioi.mpr (by positivity)
  have hlog : Tendsto (Jp' p) (𝓝[>] (0:ℝ)) atBot := by
    have h := tendsto_log_nhdsGT_zero.comp hA
    unfold Jp'
    simpa only [Function.comp_def] using h
  have h2 : Tendsto (fun u : ℝ => ((d:ℝ) - 1) * Jp' p u) (𝓝[>] (0:ℝ)) atBot :=
    Tendsto.const_mul_atBot hd1 hlog
  have h3 : Tendsto (fun u : ℝ => -(((d:ℝ) - 1) * Jp' p u)) (𝓝[>] (0:ℝ)) atTop :=
    tendsto_neg_atTop_iff.mpr h2
  exact h3.atTop_add h1

/-- There is a point near `0` where `h_{p,d}` is positive. -/
private theorem exists_pos_near_zero (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ a, 0 < a ∧ a < rStar d ∧ 0 < hpd p d a := by
  have hus0 := rStar_pos hd
  have hev := (hpd_tendsto_atTop_zero hd hp0 hp1).eventually (eventually_gt_atTop 0)
  have hIoo : Set.Ioo (0:ℝ) (rStar d) ∈ 𝓝[>] (0:ℝ) :=
    mem_nhdsWithin.mpr ⟨Set.Iio (rStar d), isOpen_Iio, hus0, by
      rintro x ⟨hx2, hx0⟩; exact ⟨hx0, hx2⟩⟩
  have hev2 : ∀ᶠ u in 𝓝[>] (0:ℝ), u ∈ Set.Ioo (0:ℝ) (rStar d) :=
    eventually_of_mem hIoo (fun u hu => hu)
  obtain ⟨a, hapos, hamem⟩ := (hev.and hev2).exists
  exact ⟨a, hamem.1, hamem.2, hapos⟩

/-- `lem:contact-points` ingredient (left zero): for `p < p_*` there is `u₋ ∈ (0,r_*)` with
`h_{p,d}(u₋) = 0`, and `h_{p,d} > 0` on `(0,u₋)`. -/
theorem hpd_left_zero (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp : p < pStar d) :
    ∃ um, 0 < um ∧ um < rStar d ∧ hpd p d um = 0 ∧ ∀ u, 0 < u → u < um → 0 < hpd p d u := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  have hneg : hpd p d (rStar d) < 0 := (hpd_rStar_neg_iff hd hp0 hp1).mpr hp
  obtain ⟨a, ha0, haus, hapos⟩ := exists_pos_near_zero hd hp0 hp1
  -- continuity on `[a, r_*] ⊆ (0,1)`
  have hsub : Set.Icc a (rStar d) ⊆ Set.Ioo (0:ℝ) 1 := by
    intro x hx; exact ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hus1⟩
  have hcont : ContinuousOn (hpd p d) (Set.Icc a (rStar d)) :=
    (hpd_continuousOn hd hp0 hp1).mono hsub
  -- IVT: `hpd a > 0 > hpd r_*` gives a zero in `(a, r_*)`
  have hmem : (0:ℝ) ∈ Set.Ioo (hpd p d (rStar d)) (hpd p d a) := ⟨hneg, hapos⟩
  have hivt := intermediate_value_Ioo' (le_of_lt haus) hcont
  obtain ⟨c, hc1, hc2⟩ := hivt hmem
  refine ⟨c, lt_trans ha0 hc1.1, hc1.2, hc2, ?_⟩
  -- positivity on `(0,c)` from strict antitonicity on `(0,r_*)`
  intro u hu0 huc
  have hu_us : u < rStar d := lt_trans huc hc1.2
  have hanti := hpd_strictAntiOn hd hp0 hp1
  have hcuc : hpd p d c < hpd p d u :=
    hanti ⟨hu0, hu_us⟩ ⟨lt_trans ha0 hc1.1, hc1.2⟩ huc
  rw [hc2] at hcuc; exact hcuc

/-- `s - D·log s → +∞` as `s → +∞`, for `0 < D`. -/
private theorem tendsto_id_sub_const_mul_log_atTop {D : ℝ} (hD : 0 < D) :
    Tendsto (fun s : ℝ => s - D * Real.log s) atTop atTop := by
  -- From `log =o[atTop] id` with constant `1/(2D)`: eventually `‖log s‖ ≤ (1/(2D))*‖s‖`.
  have hlit := Real.isLittleO_log_id_atTop.def (c := 1 / (2 * D)) (by positivity)
  have hbound : ∀ᶠ s : ℝ in atTop, s / 2 ≤ s - D * Real.log s := by
    filter_upwards [hlit, eventually_gt_atTop (0:ℝ)] with s hs hspos
    have hsabs : ‖s‖ = s := by rw [Real.norm_eq_abs, abs_of_pos hspos]
    have hid : ‖(id : ℝ → ℝ) s‖ = s := by simpa [id] using hsabs
    rw [hid] at hs
    -- `D * log s ≤ D * ‖log s‖ ≤ D * ((1/(2D)) * s) = s/2`
    have h1 : D * Real.log s ≤ D * ‖Real.log s‖ :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hD.le
    have h2 : D * ‖Real.log s‖ ≤ D * ((1 / (2 * D)) * s) :=
      mul_le_mul_of_nonneg_left hs hD.le
    have h3 : D * ((1 / (2 * D)) * s) = s / 2 := by field_simp
    have : D * Real.log s ≤ s / 2 := by rw [← h3]; exact le_trans h1 h2
    linarith
  have hhalf : Tendsto (fun s : ℝ => s / 2) atTop atTop :=
    Filter.tendsto_id.atTop_div_const (by norm_num)
  exact tendsto_atTop_mono' atTop hbound hhalf

/-- As `u → 1⁻`, `h_{p,d}(u) → +∞`. -/
theorem hpd_tendsto_atTop_one (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (hpd p d) (𝓝[<] (1:ℝ)) atTop := by
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by have := one_lt_d hd; linarith
  -- Dominant part: `(1-u)⁻¹ + (d-1)·log(1-u) → +∞`.
  have hdom : Tendsto (fun u : ℝ => (1 - u)⁻¹ + ((d:ℝ) - 1) * Real.log (1 - u))
      (𝓝[<] (1:ℝ)) atTop := by
    -- inner: `(1-u)⁻¹ → +∞`
    have h1u : Tendsto (fun u : ℝ => 1 - u) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hcont : Continuous (fun u : ℝ => 1 - u) := by fun_prop
        have ht := hcont.tendsto (1:ℝ)
        simp only [sub_self] at ht
        exact ht.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact Set.mem_Ioi.mpr (by simp only [Set.mem_Iio] at hu; linarith)
    have hinner : Tendsto (fun u : ℝ => (1 - u)⁻¹) (𝓝[<] (1:ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp h1u
    -- outer: `s - (d-1)·log s → +∞`, composed with `s = (1-u)⁻¹`
    have houter := tendsto_id_sub_const_mul_log_atTop hd1
    have hcomp := houter.comp hinner
    refine hcomp.congr' ?_
    filter_upwards [Ioo_mem_nhdsWithin_one] with u hu
    have h1u0 : (0:ℝ) < 1 - u := by linarith [hu.2]
    have : Real.log ((1 - u)⁻¹) = -Real.log (1 - u) := Real.log_inv _
    simp only [Function.comp_def]
    rw [this]; ring
  -- Convergent tail: `-(d-1)·log u + (d-1)·(log p - log(1-p)) → (d-1)·(log p - log(1-p))`.
  have htail : Tendsto
      (fun u : ℝ => -((d:ℝ) - 1) * Real.log u + ((d:ℝ) - 1) * (Real.log p - Real.log (1 - p)))
      (𝓝[<] (1:ℝ)) (𝓝 (((d:ℝ) - 1) * (Real.log p - Real.log (1 - p)))) := by
    have hca : ContinuousAt
        (fun u : ℝ => -((d:ℝ) - 1) * Real.log u
          + ((d:ℝ) - 1) * (Real.log p - Real.log (1 - p))) 1 := by
      apply ContinuousAt.add
      · exact (Real.continuousAt_log one_ne_zero).const_mul _
      · exact continuousAt_const
    have := hca.tendsto
    simp only [Real.log_one, mul_zero, zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- Combine: `hpd = dominant + tail`, atTop + (𝓝 c).
  have hsum := hdom.atTop_add htail
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsWithin_one] with u hu
  have hu0 : (0:ℝ) < u := hu.1
  have hu1 : u < 1 := hu.2
  have h1u0 : (0:ℝ) < 1 - u := by linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1pne : (1:ℝ) - p ≠ 0 := by linarith
  rw [hpd_eq hu0 hu1, Jp']
  -- `log(u(1-p)/((1-u)p)) = log u + log(1-p) - log(1-u) - log p`
  have hlogexp : Real.log (u * (1 - p) / ((1 - u) * p))
      = Real.log u + Real.log (1 - p) - Real.log (1 - u) - Real.log p := by
    rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (ne_of_gt hu0) (by linarith),
        Real.log_mul (ne_of_gt h1u0) hpne]
    ring
  rw [hlogexp]; ring

/-- There is a point near `1` where `h_{p,d}` is positive. -/
private theorem exists_pos_near_one (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ b, rStar d < b ∧ b < 1 ∧ 0 < hpd p d b := by
  have hus1 := rStar_lt_one hd
  have hev := (hpd_tendsto_atTop_one hd hp0 hp1).eventually (eventually_gt_atTop 0)
  have hIoo : Set.Ioo (rStar d) (1:ℝ) ∈ 𝓝[<] (1:ℝ) :=
    mem_nhdsWithin.mpr ⟨Set.Ioi (rStar d), isOpen_Ioi, hus1, by
      rintro x ⟨hx2, hx1⟩; exact ⟨hx2, hx1⟩⟩
  have hev2 : ∀ᶠ u in 𝓝[<] (1:ℝ), u ∈ Set.Ioo (rStar d) (1:ℝ) :=
    eventually_of_mem hIoo (fun u hu => hu)
  obtain ⟨b, hbpos, hbmem⟩ := (hev.and hev2).exists
  exact ⟨b, hbmem.1, hbmem.2, hbpos⟩

/-- `lem:contact-points` ingredient (right zero): for `p < p_*` there is `u₊ ∈ (r_*,1)` with
`h_{p,d}(u₊) = 0`, and `h_{p,d} > 0` on `(u₊,1)`. -/
theorem hpd_right_zero (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp : p < pStar d) :
    ∃ up, rStar d < up ∧ up < 1 ∧ hpd p d up = 0 ∧ ∀ u, up < u → u < 1 → 0 < hpd p d u := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  have hneg : hpd p d (rStar d) < 0 := (hpd_rStar_neg_iff hd hp0 hp1).mpr hp
  obtain ⟨b, hbus, hb1, hbpos⟩ := exists_pos_near_one hd hp0 hp1
  -- continuity on `[r_*, b] ⊆ (0,1)`
  have hsub : Set.Icc (rStar d) b ⊆ Set.Ioo (0:ℝ) 1 := by
    intro x hx; exact ⟨lt_of_lt_of_le hus0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
  have hcont : ContinuousOn (hpd p d) (Set.Icc (rStar d) b) :=
    (hpd_continuousOn hd hp0 hp1).mono hsub
  -- IVT: `hpd r_* < 0 < hpd b` gives a zero in `(r_*, b)`
  have hmem : (0:ℝ) ∈ Set.Ioo (hpd p d (rStar d)) (hpd p d b) := ⟨hneg, hbpos⟩
  have hivt := intermediate_value_Ioo (le_of_lt hbus) hcont
  obtain ⟨c, hc1, hc2⟩ := hivt hmem
  refine ⟨c, hc1.1, lt_trans hc1.2 hb1, hc2, ?_⟩
  -- positivity on `(c,1)` from strict monotonicity on `(r_*,1)`
  intro u hcu hu1
  have hu_us : rStar d < u := lt_trans hc1.1 hcu
  have hmono := hpd_strictMonoOn hd hp0 hp1
  have hcuc : hpd p d c < hpd p d u :=
    hmono ⟨hc1.1, lt_trans hc1.2 hb1⟩ ⟨hu_us, hu1⟩ hcu
  rw [hc2] at hcuc; exact hcuc

end

/-! ### Second derivative of `φ_{p,d}` (rpow). -/

section
variable {p : ℝ} {d : ℕ}

/-- The explicit second-derivative formula `φ_{p,d}''(x) = h_{p,d}(z)/(d² z^{2d-1})`,
`u = x^{1/d}`. -/
noncomputable def phi'' (p : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  hpd p d (Real.rpow x (1 / (d:ℝ))) /
    ((d:ℝ) ^ 2 * (Real.rpow x (1 / (d:ℝ))) ^ (2 * d - 1))

/-- `φ_{p,d}''(x) > 0` iff `h_{p,d}(x^{1/d}) > 0` (positive denominator). -/
theorem phi''_pos_iff (hd : 2 ≤ d) {x : ℝ} (hx0 : 0 < x) :
    0 < phi'' p d x ↔ 0 < hpd p d (Real.rpow x (1 / (d:ℝ))) := by
  have hdpos : (0:ℝ) < (d:ℝ) := dpos hd
  have hu0 : 0 < Real.rpow x (1 / (d:ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hden : 0 < ((d:ℝ) ^ 2 * (Real.rpow x (1 / (d:ℝ))) ^ (2 * d - 1)) := by positivity
  unfold phi''
  rw [div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact h
    · exact absurd hden (not_lt.mpr (le_of_lt h))
  · intro h; exact Or.inl ⟨h, hden⟩

/-- `φ_{p,d}''(x) < 0` iff `h_{p,d}(x^{1/d}) < 0`. -/
theorem phi''_neg_iff (hd : 2 ≤ d) {x : ℝ} (hx0 : 0 < x) :
    phi'' p d x < 0 ↔ hpd p d (Real.rpow x (1 / (d:ℝ))) < 0 := by
  have hdpos : (0:ℝ) < (d:ℝ) := dpos hd
  have hu0 : 0 < Real.rpow x (1 / (d:ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hden : 0 < ((d:ℝ) ^ 2 * (Real.rpow x (1 / (d:ℝ))) ^ (2 * d - 1)) := by positivity
  unfold phi''
  rw [div_neg_iff]
  constructor
  · rintro (⟨_, hb⟩ | ⟨ha, _⟩)
    · exact absurd hb (not_lt.mpr (le_of_lt hden))
    · exact ha
  · intro h; exact Or.inr ⟨h, hden⟩

/-- `HasDerivAt (deriv (φ_{p,d})) (φ_{p,d}''(x)) x` for `x ∈ (0,1)`. -/
theorem hasDerivAt_phi'' (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (deriv (phi p d)) (phi'' p d x) x := by
  have hdpos := dpos hd
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hu0 : 0 < Real.rpow x (1/(d:ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hune : Real.rpow x (1/(d:ℝ)) ≠ 0 := ne_of_gt hu0
  have hu1 : Real.rpow x (1/(d:ℝ)) < 1 := by
    have : Real.rpow x (1/(d:ℝ)) < Real.rpow 1 (1/(d:ℝ)) :=
      Real.rpow_lt_rpow hx0.le hx1 (by positivity)
    simpa using this
  have h1une : 1 - Real.rpow x (1/(d:ℝ)) ≠ 0 := ne_of_gt (by linarith)
  -- `u^d = x`
  have huxd : (Real.rpow x (1/(d:ℝ))) ^ d = x := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hx0.le (by omega)
  -- `deriv (phi p d)` agrees with the explicit derivative `g` on `(0,1)`
  have hg_eq : deriv (phi p d) =ᶠ[𝓝 x]
      (fun y => Jp' p (Real.rpow y (1/(d:ℝ))) * ((1/(d:ℝ)) * Real.rpow y (1/(d:ℝ) - 1))) := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy
    exact (hasDerivAt_phi hd hp0 hp1 hy.1 hy.2).deriv
  -- product/chain rule for `g`
  have hrpow_a : HasDerivAt (fun y => Real.rpow y (1/(d:ℝ)))
      ((1/(d:ℝ)) * Real.rpow x (1/(d:ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hxne)
  have hA : HasDerivAt (fun y => Jp' p (Real.rpow y (1/(d:ℝ))))
      (Jp'' (Real.rpow x (1/(d:ℝ))) * ((1/(d:ℝ)) * Real.rpow x (1/(d:ℝ) - 1))) x := by
    have := (hasDerivAt_Jp' hp0 hp1 hu0 hu1).comp x hrpow_a
    simpa [Function.comp_def] using this
  have hrpow_a1 : HasDerivAt (fun y => Real.rpow y (1/(d:ℝ) - 1))
      ((1/(d:ℝ) - 1) * Real.rpow x (1/(d:ℝ) - 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hxne)
  have hB : HasDerivAt (fun y => (1/(d:ℝ)) * Real.rpow y (1/(d:ℝ) - 1))
      ((1/(d:ℝ)) * ((1/(d:ℝ) - 1) * Real.rpow x (1/(d:ℝ) - 1 - 1))) x :=
    hrpow_a1.const_mul (1/(d:ℝ))
  have hg := hA.mul hB
  have hgoal := hg.congr_of_eventuallyEq hg_eq
  convert hgoal using 1
  all_goals try rfl
  -- rewrite the rpow powers in terms of `u = rpow x (1/d)` and `x`
  -- (proved on `^` and transferred to `Real.rpow` by `exact`, which uses defeq)
  have e1 : Real.rpow x (1/(d:ℝ) - 1) = Real.rpow x (1/(d:ℝ)) * x⁻¹ := by
    have : x ^ (1/(d:ℝ) - 1) = x ^ (1/(d:ℝ)) * x⁻¹ := by
      rw [Real.rpow_sub hx0, Real.rpow_one, div_eq_mul_inv]
    exact this
  have e2 : Real.rpow x (1/(d:ℝ) - 1 - 1) = Real.rpow x (1/(d:ℝ)) * x⁻¹ * x⁻¹ := by
    have : x ^ (1/(d:ℝ) - 1 - 1) = x ^ (1/(d:ℝ)) * x⁻¹ * x⁻¹ := by
      rw [Real.rpow_sub hx0, Real.rpow_one, show x ^ (1/(d:ℝ) - 1) = x ^ (1/(d:ℝ)) * x⁻¹ from by
        rw [Real.rpow_sub hx0, Real.rpow_one, div_eq_mul_inv], div_eq_mul_inv]
    exact this
  -- `u^(2d-1) = x^2 * u⁻¹`
  have hpow : (Real.rpow x (1/(d:ℝ))) ^ (2 * d - 1) = x ^ 2 * (Real.rpow x (1/(d:ℝ)))⁻¹ := by
    have h2d : (Real.rpow x (1/(d:ℝ))) ^ (2 * d) = x ^ 2 := by
      rw [show 2 * d = d * 2 from by ring, pow_mul, huxd]
    have hsucc : (Real.rpow x (1/(d:ℝ))) ^ (2 * d)
        = (Real.rpow x (1/(d:ℝ))) ^ (2 * d - 1) * Real.rpow x (1/(d:ℝ)) := by
      rw [← pow_succ]; congr 1; omega
    rw [h2d] at hsucc
    rw [hsucc, mul_assoc, mul_inv_cancel₀ hune, mul_one]
  rw [phi'', e1, e2, hpow, hpd, Jp'']
  field_simp
  ring

end

/-! ### Continuity of `φ_{p,d}` and the boundary slope limits (towards `lem:contact-points`). -/

section
variable {p : ℝ} {d : ℕ}

/-- As `u → 0⁺`, `J_p'(u) → -∞`. -/
theorem Jp'_tendsto_atBot (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (Jp' p) (𝓝[>] (0:ℝ)) Filter.atBot := by
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hA : Filter.Tendsto (fun u : ℝ => u * (1 - p) / ((1 - u) * p)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hca : ContinuousAt (fun u : ℝ => u * (1 - p) / ((1 - u) * p)) 0 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hpne)
      have := hca.tendsto
      simp only [zero_mul, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsWithin_zero] with u hu
      have hu0 : (0:ℝ) < u := hu.1
      have h1u : (0:ℝ) < 1 - u := by linarith [hu.2]
      have hp1' : (0:ℝ) < 1 - p := by linarith
      exact Set.mem_Ioi.mpr (by positivity)
  have h := tendsto_log_nhdsGT_zero.comp hA
  unfold Jp'
  simpa only [Function.comp_def] using h

/-- As `x → 0⁺`, `φ_{p,d}'(x) → -∞`. -/
theorem phi'_tendsto_atBot (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (deriv (phi p d)) (𝓝[>] (0:ℝ)) Filter.atBot := by
  have hdpos := dpos hd
  have heq : deriv (phi p d) =ᶠ[𝓝[>] (0:ℝ)]
      (fun x => Jp' p (Real.rpow x (1/(d:ℝ))) * ((1/(d:ℝ)) * Real.rpow x (1/(d:ℝ) - 1))) := by
    filter_upwards [Ioo_mem_nhdsWithin_zero] with x hx
    exact (hasDerivAt_phi hd hp0 hp1 hx.1 hx.2).deriv
  rw [Filter.tendsto_congr' heq]
  -- `x ↦ x^{1/d} → 0⁺`
  have hu : Filter.Tendsto (fun x : ℝ => Real.rpow x (1/(d:ℝ))) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc := (Real.continuousAt_rpow_const 0 (1/(d:ℝ)) (Or.inr (by positivity))).tendsto
      rw [Real.zero_rpow (ne_of_gt (by positivity : (0:ℝ) < 1/(d:ℝ)))] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hx _)
  have h1 : Filter.Tendsto (fun x => Jp' p (Real.rpow x (1/(d:ℝ)))) (𝓝[>] (0:ℝ)) Filter.atBot :=
    (Jp'_tendsto_atBot hp0 hp1).comp hu
  -- `x ↦ x^{1/d-1} → +∞`
  have hpos : (0:ℝ) < 1 - 1/(d:ℝ) := by
    have : (1:ℝ)/(d:ℝ) < 1 := by rw [div_lt_one hdpos]; have := one_lt_d hd; linarith
    linarith
  have hbase : Filter.Tendsto (fun x : ℝ => Real.rpow x (1 - 1/(d:ℝ))) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc := (Real.continuousAt_rpow_const 0 (1 - 1/(d:ℝ)) (Or.inr hpos.le)).tendsto
      rw [Real.zero_rpow (ne_of_gt hpos)] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hx _)
  have hinv : Filter.Tendsto (fun x : ℝ => (Real.rpow x (1 - 1/(d:ℝ)))⁻¹) (𝓝[>] (0:ℝ)) Filter.atTop := by
    have := tendsto_inv_nhdsGT_zero.comp hbase
    simpa [Function.comp_def] using this
  have hee : (fun x : ℝ => (Real.rpow x (1 - 1/(d:ℝ)))⁻¹) =ᶠ[𝓝[>] (0:ℝ)]
      (fun x => Real.rpow x (1/(d:ℝ) - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h := Real.rpow_neg (le_of_lt hx) (1 - 1/(d:ℝ))
    rw [show (1:ℝ)/(d:ℝ) - 1 = -(1 - 1/(d:ℝ)) from by ring]
    exact h.symm
  have hrpow : Filter.Tendsto (fun x : ℝ => Real.rpow x (1/(d:ℝ) - 1)) (𝓝[>] (0:ℝ)) Filter.atTop :=
    hinv.congr' hee
  have h2 : Filter.Tendsto (fun x => (1/(d:ℝ)) * Real.rpow x (1/(d:ℝ) - 1)) (𝓝[>] (0:ℝ)) Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hrpow
  exact h1.atBot_mul_atTop₀ h2

/-- As `u → 1⁻`, `J_p'(u) → +∞`. -/
theorem Jp'_tendsto_atTop_one (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (Jp' p) (𝓝[<] (1:ℝ)) Filter.atTop := by
  have hpne : p ≠ 0 := ne_of_gt hp0
  have harg : Filter.Tendsto (fun u : ℝ => u * (1 - p) / ((1 - u) * p)) (𝓝[<] (1:ℝ)) Filter.atTop := by
    have h1u : Filter.Tendsto (fun u : ℝ => 1 - u) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hcont : Continuous (fun u : ℝ => 1 - u) := by fun_prop
        have ht := hcont.tendsto (1:ℝ)
        simp only [sub_self] at ht
        exact ht.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact Set.mem_Ioi.mpr (by simp only [Set.mem_Iio] at hu; linarith)
    have hinv : Filter.Tendsto (fun u : ℝ => (1 - u)⁻¹) (𝓝[<] (1:ℝ)) Filter.atTop :=
      tendsto_inv_nhdsGT_zero.comp h1u
    have hnum : Filter.Tendsto (fun u : ℝ => u * (1 - p) / p) (𝓝[<] (1:ℝ)) (𝓝 ((1 - p) / p)) := by
      have hca : ContinuousAt (fun u : ℝ => u * (1 - p) / p) 1 :=
        ((continuous_id.mul continuous_const).div_const p).continuousAt
      have := hca.tendsto
      rw [show (1:ℝ) * (1 - p) / p = (1 - p) / p from by ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hpos : (0:ℝ) < (1 - p) / p := by have := sub_pos.mpr hp1; positivity
    refine (hinv.atTop_mul_pos hpos hnum).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hune : (1:ℝ) - u ≠ 0 := ne_of_gt (by simp only [Set.mem_Iio] at hu; linarith)
    field_simp
  have h := tendsto_log_atTop.comp harg
  unfold Jp'
  simpa only [Function.comp_def] using h

/-- As `x → 1⁻`, `φ_{p,d}'(x) → +∞`. -/
theorem phi'_tendsto_atTop (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (deriv (phi p d)) (𝓝[<] (1:ℝ)) Filter.atTop := by
  have hdpos := dpos hd
  have heq : deriv (phi p d) =ᶠ[𝓝[<] (1:ℝ)]
      (fun x => Jp' p (Real.rpow x (1/(d:ℝ))) * ((1/(d:ℝ)) * Real.rpow x (1/(d:ℝ) - 1))) := by
    filter_upwards [Ioo_mem_nhdsWithin_one] with x hx
    exact (hasDerivAt_phi hd hp0 hp1 hx.1 hx.2).deriv
  rw [Filter.tendsto_congr' heq]
  have hu : Filter.Tendsto (fun x : ℝ => Real.rpow x (1/(d:ℝ))) (𝓝[<] (1:ℝ)) (𝓝[<] (1:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc := (Real.continuousAt_rpow_const 1 (1/(d:ℝ)) (Or.inl one_ne_zero)).tendsto
      rw [Real.one_rpow] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsWithin_one] with x hx
      exact Set.mem_Iio.mpr (Real.rpow_lt_one hx.1.le hx.2 (by positivity))
  have h1 : Filter.Tendsto (fun x => Jp' p (Real.rpow x (1/(d:ℝ)))) (𝓝[<] (1:ℝ)) Filter.atTop :=
    (Jp'_tendsto_atTop_one hp0 hp1).comp hu
  have h2 : Filter.Tendsto (fun x => (1/(d:ℝ)) * Real.rpow x (1/(d:ℝ) - 1)) (𝓝[<] (1:ℝ))
      (𝓝 (1/(d:ℝ))) := by
    have hca : ContinuousAt (fun x : ℝ => (1/(d:ℝ)) * Real.rpow x (1/(d:ℝ) - 1)) 1 :=
      (Real.continuousAt_rpow_const 1 (1/(d:ℝ) - 1) (Or.inl one_ne_zero)).const_mul (1/(d:ℝ))
    have := hca.tendsto
    rw [show Real.rpow 1 (1/(d:ℝ) - 1) = 1 from Real.one_rpow _, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h1.atTop_mul_pos (by positivity) h2

/-- `φ_{p,d}` is continuous on `[0,1]`. -/
theorem phi_continuousOn_Icc (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (phi p d) (Set.Icc 0 1) := by
  have hg : ContinuousOn (fun x => Real.rpow x (1/(d:ℝ))) (Set.Icc 0 1) := fun x _ =>
    (Real.continuousAt_rpow_const x (1/(d:ℝ)) (Or.inr (by positivity))).continuousWithinAt
  have hmaps : Set.MapsTo (fun x => Real.rpow x (1/(d:ℝ))) (Set.Icc 0 1) (Set.Icc 0 1) := by
    intro x hx
    refine ⟨Real.rpow_nonneg hx.1 _, ?_⟩
    calc Real.rpow x (1/(d:ℝ)) ≤ Real.rpow 1 (1/(d:ℝ)) := Real.rpow_le_rpow hx.1 hx.2 (by positivity)
      _ = 1 := by simp
  exact (continuousOn_Jp_Icc hp0 hp1).comp hg hmaps

end

/-! ### `lem:convexity-defect`(c): endpoint-inclusive monotonicity and the unique minimum -/

/-- `h_{p,d}` is strictly decreasing on `(0,r_*]` — the endpoint-inclusive form of
`hpd_strictAntiOn`, needed to compare `h(u)` with its minimum value `h(r_*)`. -/
theorem hpd_strictAntiOn_Ioc {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (hpd p d) (Set.Ioc 0 (rStar d)) := by
  have hus1 := rStar_lt_one hd
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioc _ _)
    (fun u hu => ((hasDerivAt_hpd hd hp0 hp1 hu.1
      (lt_of_le_of_lt hu.2 hus1)).continuousAt.continuousWithinAt))
    (f' := fun u => ((d : ℝ) * (u - rStar d)) / (u * (1 - u) ^ 2))
  · intro u hu
    rw [interior_Ioc] at hu
    exact (hasDerivAt_hpd hd hp0 hp1 hu.1 (lt_trans hu.2 hus1)).hasDerivWithinAt
  · intro u hu
    rw [interior_Ioc] at hu
    have hd0 := dpos hd
    have h1u : (0:ℝ) < 1 - u := by linarith [lt_trans hu.2 hus1]
    have hden : (0:ℝ) < u * (1 - u) ^ 2 := mul_pos hu.1 (pow_pos h1u 2)
    have hnum : (d : ℝ) * (u - rStar d) < 0 :=
      mul_neg_of_pos_of_neg hd0 (by linarith [hu.2])
    exact div_neg_of_neg_of_pos hnum hden

/-- `h_{p,d}` is strictly increasing on `[r_*,1)` — the endpoint-inclusive form of
`hpd_strictMonoOn`. -/
theorem hpd_strictMonoOn_Ico {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    StrictMonoOn (hpd p d) (Set.Ico (rStar d) 1) := by
  have hus0 := rStar_pos hd
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ico _ _)
    (fun u hu => ((hasDerivAt_hpd hd hp0 hp1 (lt_of_lt_of_le hus0 hu.1)
      hu.2).continuousAt.continuousWithinAt))
    (f' := fun u => ((d : ℝ) * (u - rStar d)) / (u * (1 - u) ^ 2))
  · intro u hu
    rw [interior_Ico] at hu
    exact (hasDerivAt_hpd hd hp0 hp1 (lt_trans hus0 hu.1) hu.2).hasDerivWithinAt
  · intro u hu
    rw [interior_Ico] at hu
    have hd0 := dpos hd
    have h1u : (0:ℝ) < 1 - u := by linarith [hu.2]
    have hden : (0:ℝ) < u * (1 - u) ^ 2 := mul_pos (lt_trans hus0 hu.1) (pow_pos h1u 2)
    have hnum : 0 < (d : ℝ) * (u - rStar d) := mul_pos hd0 (by linarith [hu.1])
    exact div_pos hnum hden

/-- **`lem:convexity-defect`(c), unique minimum**: `r_*` is the *strict* minimum
point of `h_{p,d}` on `(0,1)`.  At every other interior `u` the value is strictly larger, so
the minimum value `h_{p,d}(r_*)` of `hpd_rStar` is attained at `r_*` alone. -/
theorem hpd_rStar_lt_of_ne {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hne : u ≠ rStar d) :
    hpd p d (rStar d) < hpd p d u := by
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  rcases lt_trichotomy u (rStar d) with h | h | h
  · exact hpd_strictAntiOn_Ioc hd hp0 hp1 ⟨hu0, h.le⟩ ⟨hus0, le_rfl⟩ h
  · exact absurd h hne
  · exact hpd_strictMonoOn_Ico hd hp0 hp1 ⟨le_rfl, hus1⟩ ⟨h.le, hu1⟩ h

/-! ### `lem:convexity-defect`(e): the convexity defect and `φ_{p,d}` above the threshold `p_*` -/

/-- **`h_{p,d} ≥ 0` above the threshold.**  For `p ≥ p_*` the convexity defect is nonnegative
on all of `(0,1)`: its minimum is at `r_*`, where it is `≥ 0` exactly when `p ≥ p_*`. -/
theorem hpd_nonneg_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hps : pStar d ≤ p) (hp1 : p < 1)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : 0 ≤ hpd p d u := by
  have hp0 : 0 < p := lt_of_lt_of_le (pStar_pos hd) hps
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  have hstar : 0 ≤ hpd p d (rStar d) := (hpd_rStar_nonneg_iff hd hp0 hp1).mpr hps
  rcases lt_trichotomy u (rStar d) with h | h | h
  · exact le_trans hstar
      (le_of_lt (hpd_strictAntiOn_Ioc hd hp0 hp1 ⟨hu0, h.le⟩ ⟨hus0, le_refl _⟩ h))
  · rw [h]; exact hstar
  · exact le_trans hstar
      (le_of_lt (hpd_strictMonoOn_Ico hd hp0 hp1 ⟨le_refl _, hus1⟩ ⟨h.le, hu1⟩ h))

/-- **Convexity of the Lubetzky–Zhao graph above the threshold.**  For `p ≥ p_*` the map
`φ_{p,d}` is convex on the whole of `[0,1]`.  (`LZBoundary/PhiConvex.lean` deliberately stops at
the pointwise sign of `φ''` and its one-sided strict-convexity packages; this is the
full-interval packaging, needed to produce supporting lines at *every* interior abscissa
— in particular at the exceptional one, where no Lubetzky–Zhao boundary arc is available.) -/
theorem convexOn_phi_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hps : pStar d ≤ p) (hp1 : p < 1) :
    ConvexOn ℝ (Set.Icc 0 1) (phi p d) := by
  have hp0 : 0 < p := lt_of_lt_of_le (pStar_pos hd) hps
  refine convexOn_of_deriv2_nonneg (convex_Icc 0 1) (phi_continuousOn_Icc hd hp0 hp1)
    ?_ ?_ ?_ <;> rw [interior_Icc]
  · exact fun x hx =>
      (hasDerivAt_phi hd hp0 hp1 hx.1 hx.2).differentiableAt.differentiableWithinAt
  · exact fun x hx =>
      (hasDerivAt_phi'' hd hp0 hp1 hx.1 hx.2).differentiableAt.differentiableWithinAt
  · intro x hx
    have he : deriv^[2] (phi p d) x = phi'' p d x := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact (hasDerivAt_phi'' hd hp0 hp1 hx.1 hx.2).deriv
    rw [he]
    have hu0 : 0 < Real.rpow x (1/(d:ℝ)) := Real.rpow_pos_of_pos hx.1 _
    have hu1 : Real.rpow x (1/(d:ℝ)) < 1 := by
      have h : Real.rpow x (1/(d:ℝ)) < Real.rpow 1 (1/(d:ℝ)) :=
        Real.rpow_lt_rpow hx.1.le hx.2 (by have := dpos hd; positivity)
      simpa using h
    rw [← not_lt, phi''_neg_iff hd hx.1, not_lt]
    exact hpd_nonneg_of_pStar_le hd hps hp1 hu0 hu1

/-! ### One-sided strict convexity of `φ_{p,d}` from the sign of `φ_{p,d}''` -/

/-- `φ_{p,d}` is strictly convex on `[c,1]` when `φ''>0` on `(c,1)`. -/
theorem strictConvexOn_phi_right {d : ℕ} {p c : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    (hc0 : 0 < c) (_hc1 : c < 1) (hconv : ∀ x ∈ Set.Ioo c 1, 0 < phi'' p d x) :
    StrictConvexOn ℝ (Set.Icc c 1) (phi p d) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc c 1)
    ((phi_continuousOn_Icc hd hp0 hp1).mono (Set.Icc_subset_Icc hc0.le le_rfl))
  rw [interior_Icc]; intro x hx
  have he : deriv^[2] (phi p d) x = phi'' p d x := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    exact (hasDerivAt_phi'' hd hp0 hp1 (lt_trans hc0 hx.1) hx.2).deriv
  rw [he]; exact hconv x hx

/-- `φ_{p,d}` is strictly convex on `[0,c]` when `φ''>0` on `(0,c)`. -/
theorem strictConvexOn_phi_left {d : ℕ} {p c : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    (_hc0 : 0 < c) (hc1 : c < 1) (hconv : ∀ x ∈ Set.Ioo (0:ℝ) c, 0 < phi'' p d x) :
    StrictConvexOn ℝ (Set.Icc 0 c) (phi p d) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc 0 c)
    ((phi_continuousOn_Icc hd hp0 hp1).mono (Set.Icc_subset_Icc le_rfl hc1.le))
  rw [interior_Icc]; intro x hx
  have he : deriv^[2] (phi p d) x = phi'' p d x := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    exact (hasDerivAt_phi'' hd hp0 hp1 hx.1 (lt_trans hx.2 hc1)).deriv
  rw [he]; exact hconv x hx

/-! ### `lem:convexity-defect`(f)–(g): the two zeros below the threshold `p_*` -/

/-- For `0 < x < c^d` the `d`-th root `x^{1/d}` stays below `c`. -/
private theorem rpow_inv_lt_of_lt_pow {d : ℕ} (hd : 2 ≤ d) {x c : ℝ} (hx0 : 0 < x) (hc0 : 0 < c)
    (hxc : x < c ^ d) : Real.rpow x (1 / (d:ℝ)) < c := by
  have hz : (0:ℝ) < 1 / (d:ℝ) := by have := dpos hd; positivity
  have hceq : Real.rpow (c ^ d) (1 / (d:ℝ)) = c := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hc0.le (by omega)
  calc Real.rpow x (1 / (d:ℝ)) < Real.rpow (c ^ d) (1 / (d:ℝ)) :=
        Real.rpow_lt_rpow hx0.le hxc hz
    _ = c := hceq

/-- For `c^d < x` with `0 < c` the `d`-th root `x^{1/d}` exceeds `c`. -/
private theorem lt_rpow_inv_of_pow_lt {d : ℕ} (hd : 2 ≤ d) {x c : ℝ} (hc0 : 0 < c)
    (hcx : c ^ d < x) : c < Real.rpow x (1 / (d:ℝ)) := by
  have hz : (0:ℝ) < 1 / (d:ℝ) := by have := dpos hd; positivity
  have hceq : Real.rpow (c ^ d) (1 / (d:ℝ)) = c := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hc0.le (by omega)
  calc c = Real.rpow (c ^ d) (1 / (d:ℝ)) := hceq.symm
    _ < Real.rpow x (1 / (d:ℝ)) := Real.rpow_lt_rpow (pow_nonneg hc0.le d) hcx hz

/-- **`lem:convexity-defect`(f), middle negativity**: strictly between a zero
`u₋ ∈ (0,r_*)` and a zero `u₊ ∈ (r_*,1)` of `h_{p,d}` the convexity defect is negative.  The
two witnesses are those of `hpd_left_zero` and `hpd_right_zero`, available for `p < p_*`. -/
theorem hpd_neg_of_between_zeros {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {um up : ℝ} (hum0 : 0 < um) (humus : um < rStar d) (humz : hpd p d um = 0)
    (hupus : rStar d < up) (hup1 : up < 1) (hupz : hpd p d up = 0)
    {u : ℝ} (hlo : um < u) (hhi : u < up) : hpd p d u < 0 := by
  by_cases h : u ≤ rStar d
  · have hlt := hpd_strictAntiOn_Ioc hd hp0 hp1 ⟨hum0, humus.le⟩ ⟨lt_trans hum0 hlo, h⟩ hlo
    rwa [humz] at hlt
  · have h' : rStar d < u := not_le.mp h
    have hlt := hpd_strictMonoOn_Ico hd hp0 hp1 ⟨h'.le, lt_trans hhi hup1⟩ ⟨hupus.le, hup1⟩ hhi
    rwa [hupz] at hlt

/-- **`lem:convexity-defect`(f), exactly two zeros**: a zero `u₋ ∈ (0,r_*)` and a
zero `u₊ ∈ (r_*,1)` of `h_{p,d}` exhaust the zeros in `(0,1)`.  Together with
`hpd_left_zero`, `hpd_right_zero` and `hpd_neg_of_between_zeros` this is the full statement
that for `p < p_*` the convexity defect has exactly two zeros, is positive on
`(0,u₋) ∪ (u₊,1)` and negative on `(u₋,u₊)`. -/
theorem hpd_eq_zero_iff_of_zeros {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {um up : ℝ} (hum0 : 0 < um) (humus : um < rStar d) (humz : hpd p d um = 0)
    (hupus : rStar d < up) (hup1 : up < 1) (hupz : hpd p d up = 0)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : hpd p d u = 0 ↔ u = um ∨ u = up := by
  constructor
  · intro hz
    by_contra hcon
    push Not at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    rcases lt_trichotomy u um with h | h | h
    · have hlt := hpd_strictAntiOn_Ioc hd hp0 hp1 ⟨hu0, le_trans h.le humus.le⟩
        ⟨hum0, humus.le⟩ h
      rw [humz, hz] at hlt; exact absurd hlt (lt_irrefl 0)
    · exact hne1 h
    · rcases lt_trichotomy u up with h2 | h2 | h2
      · have hlt := hpd_neg_of_between_zeros hd hp0 hp1 hum0 humus humz hupus hup1 hupz h h2
        rw [hz] at hlt; exact absurd hlt (lt_irrefl 0)
      · exact hne2 h2
      · have hlt := hpd_strictMonoOn_Ico hd hp0 hp1 ⟨hupus.le, hup1⟩
          ⟨le_trans hupus.le h2.le, hu1⟩ h2
        rw [hupz, hz] at hlt; exact absurd hlt (lt_irrefl 0)
  · rintro (rfl | rfl)
    · exact humz
    · exact hupz

/-- **`lem:convexity-defect`(g), lower interval**: below the `d`-th power of a
left zero `u₋` of `h_{p,d}` the Lubetzky–Zhao graph is strictly convex.  The positivity
hypothesis is the one `hpd_left_zero` supplies. -/
theorem strictConvexOn_phi_lower {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {um : ℝ} (hum0 : 0 < um) (hum1 : um < 1)
    (hpos : ∀ u, 0 < u → u < um → 0 < hpd p d u) :
    StrictConvexOn ℝ (Set.Icc 0 (um ^ d)) (phi p d) := by
  refine strictConvexOn_phi_left hd hp0 hp1 (pow_pos hum0 d)
    (pow_lt_one₀ hum0.le hum1 (by omega)) ?_
  intro x hx
  rw [phi''_pos_iff hd hx.1]
  exact hpos _ (Real.rpow_pos_of_pos hx.1 _) (rpow_inv_lt_of_lt_pow hd hx.1 hum0 hx.2)

/-- **`lem:convexity-defect`(g), middle interval**: between the `d`-th powers of
the two zeros `u₋ < u₊` of `h_{p,d}` the Lubetzky–Zhao graph is strictly *concave*.  This is
the concave face of the convex–concave–convex structure; the negativity hypothesis is
`hpd_neg_of_between_zeros`. -/
theorem strictConcaveOn_phi_middle {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {um up : ℝ} (hum0 : 0 < um) (humup : um < up) (hup1 : up < 1)
    (hneg : ∀ u, um < u → u < up → hpd p d u < 0) :
    StrictConcaveOn ℝ (Set.Icc (um ^ d) (up ^ d)) (phi p d) := by
  have hup0 : 0 < up := lt_trans hum0 humup
  have humd : (0:ℝ) < um ^ d := pow_pos hum0 d
  have hupd : up ^ d < 1 := pow_lt_one₀ hup0.le hup1 (by omega)
  have hsub : Set.Icc (um ^ d) (up ^ d) ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Icc_subset_Icc humd.le hupd.le
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
    ((phi_continuousOn_Icc hd hp0 hp1).mono hsub)
  rw [interior_Icc]; intro x hx
  have hx0 : 0 < x := lt_trans humd hx.1
  have hx1 : x < 1 := lt_trans hx.2 hupd
  have he : deriv^[2] (phi p d) x = phi'' p d x := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    exact (hasDerivAt_phi'' hd hp0 hp1 hx0 hx1).deriv
  rw [he, phi''_neg_iff hd hx0]
  exact hneg _ (lt_rpow_inv_of_pow_lt hd hum0 hx.1) (rpow_inv_lt_of_lt_pow hd hx0 hup0 hx.2)

/-- **`lem:convexity-defect`(g), upper interval**: above the `d`-th power of a
right zero `u₊` of `h_{p,d}` the Lubetzky–Zhao graph is strictly convex.  The positivity
hypothesis is the one `hpd_right_zero` supplies. -/
theorem strictConvexOn_phi_upper {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    {up : ℝ} (hup0 : 0 < up) (hup1 : up < 1)
    (hpos : ∀ u, up < u → u < 1 → 0 < hpd p d u) :
    StrictConvexOn ℝ (Set.Icc (up ^ d) 1) (phi p d) := by
  refine strictConvexOn_phi_right hd hp0 hp1 (pow_pos hup0 d)
    (pow_lt_one₀ hup0.le hup1 (by omega)) ?_
  intro x hx
  have hx0 : 0 < x := lt_trans (pow_pos hup0 d) hx.1
  rw [phi''_pos_iff hd hx0]
  refine hpos _ (lt_rpow_inv_of_pow_lt hd hup0 hx.1) ?_
  have hlt : Real.rpow x (1 / (d:ℝ)) < Real.rpow 1 (1 / (d:ℝ)) :=
    Real.rpow_lt_rpow hx0.le hx.2 (by have := dpos hd; positivity)
  simpa using hlt

/-! ### `lem:convexity-defect` packaged -/

/-- **`lem:convexity-defect` of `paper/paper.tex`, in one declaration.**

For every `p ∈ (0,1)` and `d ≥ 2`, with the lemma's assertions labelled (a)–(g) in order:

* (a) `h_{p,d}'(z) = d(z - r_*)/(z(1-z)^2)` on `(0,1)`;
* (b) `h_{p,d}(r_*) = d - (d-1) log((d-1)(1-p)/p)`;
* (c) `h_{p,d}` is strictly decreasing on `(0,r_*)`, strictly increasing on `(r_*,1)`, and
  has its unique minimum at `r_*`;
* (d) `φ_{p,d}''(x) = h_{p,d}(z)/(d² z^{2d-1})` for `z = x^{1/d}` (this is the definition of
  `phi''`, and `hasDerivAt_phi''` identifies it with the second derivative), so
  `φ_{p,d}''(x)` and `h_{p,d}(z)` have the same sign;
* (e) if `p ≥ p_*` then `h_{p,d} ≥ 0` on `(0,1)` and `φ_{p,d}` is convex on `[0,1]`;
* (f) if `p < p_*` then `h_{p,d}` has exactly two zeros `u₋ < r_* < u₊`, is positive on
  `(0,u₋) ∪ (u₊,1)` and negative on `(u₋,u₊)`;
* (g) accordingly `φ_{p,d}` is strictly convex on `[0,u₋^d]` and `[u₊^d,1]` and strictly
  concave on `[u₋^d,u₊^d]`.

Here the two zeros are produced existentially; `convexity_defect_zeros`
(`LZBoundary/PaperForm.lean`) states the lemma with the named zeros `uMinus p d`, `uPlus p d`.
The downstream proofs consume the individual lemmas assembled here. -/
theorem convexity_defect {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ u : ℝ, 0 < u → u < 1 →
        HasDerivAt (hpd p d) (((d : ℝ) * (u - rStar d)) / (u * (1 - u) ^ 2)) u) ∧
      hpd p d (rStar d)
          = (d : ℝ) - ((d : ℝ) - 1) * Real.log (((d : ℝ) - 1) * (1 - p) / p) ∧
      StrictAntiOn (hpd p d) (Set.Ioo 0 (rStar d)) ∧
      StrictMonoOn (hpd p d) (Set.Ioo (rStar d) 1) ∧
      (∀ u : ℝ, 0 < u → u < 1 → u ≠ rStar d → hpd p d (rStar d) < hpd p d u) ∧
      (∀ x : ℝ, 0 < x → x < 1 → HasDerivAt (deriv (phi p d)) (phi'' p d x) x) ∧
      (∀ x : ℝ, 0 < x →
        (0 < phi'' p d x ↔ 0 < hpd p d (Real.rpow x (1 / (d : ℝ)))) ∧
          (phi'' p d x < 0 ↔ hpd p d (Real.rpow x (1 / (d : ℝ))) < 0)) ∧
      (pStar d ≤ p → (∀ u : ℝ, 0 < u → u < 1 → 0 ≤ hpd p d u) ∧
        ConvexOn ℝ (Set.Icc 0 1) (phi p d)) ∧
      (p < pStar d → ∃ um up : ℝ,
        0 < um ∧ um < rStar d ∧ rStar d < up ∧ up < 1 ∧
          hpd p d um = 0 ∧ hpd p d up = 0 ∧
          (∀ u : ℝ, 0 < u → u < 1 → (hpd p d u = 0 ↔ u = um ∨ u = up)) ∧
          (∀ u : ℝ, 0 < u → u < um → 0 < hpd p d u) ∧
          (∀ u : ℝ, um < u → u < up → hpd p d u < 0) ∧
          (∀ u : ℝ, up < u → u < 1 → 0 < hpd p d u) ∧
          StrictConvexOn ℝ (Set.Icc 0 (um ^ d)) (phi p d) ∧
          StrictConcaveOn ℝ (Set.Icc (um ^ d) (up ^ d)) (phi p d) ∧
          StrictConvexOn ℝ (Set.Icc (up ^ d) 1) (phi p d)) := by
  refine ⟨fun u hu0 hu1 => hasDerivAt_hpd hd hp0 hp1 hu0 hu1, hpd_rStar hd hp0 hp1,
    hpd_strictAntiOn hd hp0 hp1, hpd_strictMonoOn hd hp0 hp1,
    fun u hu0 hu1 hne => hpd_rStar_lt_of_ne hd hp0 hp1 hu0 hu1 hne,
    fun x hx0 hx1 => hasDerivAt_phi'' hd hp0 hp1 hx0 hx1,
    fun x hx0 => ⟨phi''_pos_iff hd hx0, phi''_neg_iff hd hx0⟩,
    fun hps => ⟨fun u hu0 hu1 => hpd_nonneg_of_pStar_le hd hps hp1 hu0 hu1,
      convexOn_phi_of_pStar_le hd hps hp1⟩, fun hp => ?_⟩
  obtain ⟨um, hum0, humus, humz, humpos⟩ := hpd_left_zero hd hp0 hp
  obtain ⟨up, hupus, hup1, hupz, huppos⟩ := hpd_right_zero hd hp0 hp
  have hmid : ∀ u, um < u → u < up → hpd p d u < 0 := fun u hlo hhi =>
    hpd_neg_of_between_zeros hd hp0 hp1 hum0 humus humz hupus hup1 hupz hlo hhi
  exact ⟨um, up, hum0, humus, hupus, hup1, humz, hupz,
    fun u hu0 hu1 =>
      hpd_eq_zero_iff_of_zeros hd hp0 hp1 hum0 humus humz hupus hup1 hupz hu0 hu1,
    humpos, hmid, huppos,
    strictConvexOn_phi_lower hd hp0 hp1 hum0 (lt_trans humus (rStar_lt_one hd)) humpos,
    strictConcaveOn_phi_middle hd hp0 hp1 hum0 (lt_trans humus hupus) hup1 hmid,
    strictConvexOn_phi_upper hd hp0 hp1 (lt_trans (rStar_pos hd) hupus) hup1 huppos⟩

end UpperTailOptimizers
