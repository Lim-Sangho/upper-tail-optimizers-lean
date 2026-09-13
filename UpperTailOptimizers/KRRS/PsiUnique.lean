import UpperTailOptimizers.KRRS.PsiCritical

/-!
# Step 4: the critical point is unique

`KRRS/PsiCritical.lean` proves that every off-diagonal critical point of `ψ_d(ε,·)` is a
**strict** local maximum (`dWr < 0`).  Uniqueness is the standard consequence: between two
strict local maxima a differentiable function has to come back up through a zero of its
derivative with a nonnegative slope, and there are no such zeros.

Two preliminaries make the bookkeeping work.  First, at a critical point the exceptional
density lies *strictly between* the two arguments (`rStar_mem_Ioo_of_crit`) — otherwise `R_d`
would be monotone on the interval, `H` strictly decreasing, and `H(b) = H(a) = 0` impossible.
Consequently all critical points of `ψ_d(ε,·)` lie on the far side of `r_*` from `ε`, so `ε`
never separates two of them and `Wr d ε ·` is differentiable throughout the interval joining
them.  Second, at `ε = r_*` there are no off-diagonal critical points at all.

## Contents

* `nonneg_of_hasDerivAt_of_lt_right` — a derivative is `≥ 0` if the function is larger
  immediately to the right;
* `rStar_mem_Ioo_of_crit` — `a < r_* < b` at every critical pair;
* `crit_side` — every critical point lies across `r_*` from `ε`;
* `no_crit_rStar` — no off-diagonal critical point at `ε = r_*`;
* `crit_unique` — **Step 4**.
-/

namespace UpperTailOptimizers

open Real Set

/-! ### A one-sided derivative test -/

/-- If `f c ≤ f` immediately to the right of `c`, its derivative at `c` is `≥ 0`. -/
theorem nonneg_deriv_of_le_right {f : ℝ → ℝ} {f' c v : ℝ} (hcv : c < v)
    (hf : HasDerivAt f f' c) (h : ∀ x ∈ Set.Ioo c v, f c ≤ f x) : 0 ≤ f' := by
  have hslope : Filter.Tendsto (slope f c) (nhdsWithin c {c}ᶜ) (nhds f') :=
    hasDerivAt_iff_tendsto_slope.mp hf
  have hsub : Filter.Tendsto (slope f c) (nhdsWithin c (Set.Ioi c)) (nhds f') :=
    hslope.mono_left (nhdsWithin_mono c (fun x hx => ne_of_gt hx))
  refine ge_of_tendsto hsub ?_
  filter_upwards [Ioo_mem_nhdsGT hcv] with x hx
  have hfx : f c ≤ f x := h x hx
  rw [slope_def_field]
  exact div_nonneg (by linarith) (by linarith [hx.1])

/-- If `f ≤ f c` immediately to the left of `c`, its derivative at `c` is `≥ 0`. -/
theorem nonneg_deriv_of_le_left {f : ℝ → ℝ} {f' c u : ℝ} (huc : u < c)
    (hf : HasDerivAt f f' c) (h : ∀ x ∈ Set.Ioo u c, f x ≤ f c) : 0 ≤ f' := by
  have hslope : Filter.Tendsto (slope f c) (nhdsWithin c {c}ᶜ) (nhds f') :=
    hasDerivAt_iff_tendsto_slope.mp hf
  have hsub : Filter.Tendsto (slope f c) (nhdsWithin c (Set.Iio c)) (nhds f') :=
    hslope.mono_left (nhdsWithin_mono c (fun x hx => ne_of_lt hx))
  refine ge_of_tendsto hsub ?_
  filter_upwards [Ioo_mem_nhdsLT huc] with x hx
  have hfx : f x ≤ f c := h x hx
  rw [slope_def_field]
  exact div_nonneg_iff.mpr (Or.inr ⟨by linarith, by linarith [hx.2]⟩)

/-- **The last zero before a positive value has nonnegative derivative.** -/
theorem exists_zero_nonneg_deriv {f f' : ℝ → ℝ} {p x : ℝ} (hpx : p < x)
    (hcont : ContinuousOn f (Set.Icc p x))
    (hderiv : ∀ y ∈ Set.Icc p x, HasDerivAt f (f' y) y)
    (hp : f p ≤ 0) (hx : 0 < f x) :
    ∃ c ∈ Set.Ico p x, f c = 0 ∧ 0 ≤ f' c := by
  classical
  set S : Set ℝ := Set.Icc p x ∩ f ⁻¹' Set.Iic 0 with hSdef
  have hSne : S.Nonempty := ⟨p, ⟨Set.left_mem_Icc.mpr hpx.le, hp⟩⟩
  have hSbdd : BddAbove S := ⟨x, fun y hy => hy.1.2⟩
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  set c : ℝ := sSup S with hc
  have hcS : c ∈ S := hSclosed.csSup_mem hSne hSbdd
  have hcmem : c ∈ Set.Icc p x := hcS.1
  have hcle : f c ≤ 0 := hcS.2
  have hcx : c < x := by
    rcases lt_or_eq_of_le hcmem.2 with h | h
    · exact h
    · exfalso; rw [h] at hcle; linarith
  -- to the right of `c` the function is positive
  have hpos : ∀ y ∈ Set.Ioo c x, 0 < f y := by
    intro y hy
    by_contra hcon
    push Not at hcon
    have : y ∈ S := ⟨⟨le_trans hcmem.1 hy.1.le, hy.2.le⟩, hcon⟩
    exact absurd (le_csSup hSbdd this) (not_le.mpr hy.1)
  -- hence `f c = 0` by continuity from the right
  have hcz : f c = 0 := by
    refine le_antisymm hcle ?_
    have hmemN : Set.Icc p x ∈ nhdsWithin c (Set.Ioi c) := by
      filter_upwards [Ioo_mem_nhdsGT hcx] with y hy
      exact ⟨le_trans hcmem.1 hy.1.le, hy.2.le⟩
    have htend : Filter.Tendsto f (nhdsWithin c (Set.Ioi c)) (nhds (f c)) :=
      (hcont c hcmem).mono_left (nhdsWithin_le_iff.mpr hmemN)
    refine ge_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsGT hcx] with y hy
    exact (hpos y hy).le
  refine ⟨c, ⟨hcmem.1, hcx⟩, hcz, ?_⟩
  refine nonneg_deriv_of_le_right hcx (hderiv c hcmem) (fun y hy => ?_)
  rw [hcz]
  exact (hpos y hy).le

/-! ### The exceptional density separates the two arguments -/

/-- **At a critical pair `a < b`, the exceptional density lies strictly between.**  Otherwise
`R_d` is monotone on `[a,b]`, so `R_d < A` throughout, `H` is strictly decreasing, and
`H(b) = H(a) = 0` is impossible. -/
theorem rStar_mem_Ioo_of_crit {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hab : a < b) (hcrit : Wr d a b = 0) : rStar d ∈ Set.Ioo a b := by
  have hb0 : 0 < b := lt_trans ha0 hab
  have ha1 : a < 1 := lt_trans hab hb1
  have hne : b ≠ a := ne_of_gt hab
  obtain ⟨hRa, hRb⟩ := Rfun_lt_Aavg_of_crit hd ha0 hb1 hab hcrit
  have hsubIoo : ∀ s ∈ Set.Icc a b, 0 < s ∧ s < 1 := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hb1⟩
  have hderiv : ∀ s ∈ Set.Icc a b,
      HasDerivAt (Hfun d a b) (d2D d s * (Rfun d s - Aavg d a b)) s := fun s hs =>
    hasDerivAt_Hfun hd a b (hsubIoo s hs).1 (hsubIoo s hs).2
  have hcontAll : ContinuousOn (Hfun d a b) (Set.Icc a b) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  -- if `R_d < A` on all of `[a,b]` then `H` strictly decreases from `0` to `0`
  have hkey : (∀ s ∈ Set.Icc a b, Rfun d s < Aavg d a b) → False := by
    intro hall
    have hanti : StrictAntiOn (Hfun d a b) (Set.Icc a b) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc a b) hcontAll (fun x hx => ?_)
      rw [interior_Icc] at hx
      have hxmem : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
      rw [(hderiv x hxmem).deriv]
      have hpos : 0 < d2D d x := d2D_pos hd (hsubIoo x hxmem).1
      nlinarith [hpos, hall x hxmem]
    have := hanti (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab
    rw [Hfun_left, Hfun_right hd ha0 hb0 hne] at this
    exact lt_irrefl 0 this
  constructor
  · by_contra hcon
    push Not at hcon
    -- `r_* ≤ a`: `R_d` is antitone on `[a,b]`, so `R_d ≤ R_d a < A`
    refine hkey (fun s hs => ?_)
    rcases lt_or_eq_of_le hs.1 with hlt | heq
    · have := Rfun_strictAntiOn hd ⟨hcon, ha1⟩ ⟨le_trans hcon hs.1, (hsubIoo s hs).2⟩ hlt
      linarith
    · rw [← heq]; exact hRa
  · by_contra hcon
    push Not at hcon
    -- `b ≤ r_*`: `R_d` is monotone on `[a,b]`, so `R_d ≤ R_d b < A`
    refine hkey (fun s hs => ?_)
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · have := Rfun_strictMonoOn hd ⟨(hsubIoo s hs).1, le_trans hs.2 hcon⟩ ⟨hb0, hcon⟩ hlt
      linarith
    · rw [heq]; exact hRb

/-- Every off-diagonal critical point lies across `r_*` from `ε`. -/
theorem crit_side {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hne : z ≠ ε) (hcrit : Wr d ε z = 0) :
    (ε < rStar d ∧ rStar d < z) ∨ (z < rStar d ∧ rStar d < ε) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := rStar_mem_Ioo_of_crit hd hz0 hε1 hlt (Wr_eq_zero_swap hcrit)
    exact Or.inr ⟨this.1, this.2⟩
  · have := rStar_mem_Ioo_of_crit hd hε0 hz1 hgt hcrit
    exact Or.inl ⟨this.1, this.2⟩

/-- **At the exceptional density there is no off-diagonal critical point.** -/
theorem no_crit_rStar {d : ℕ} (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hne : z ≠ rStar d) : Wr d (rStar d) z ≠ 0 := by
  intro hcrit
  have hr0 : 0 < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  rcases crit_side hd hr0 hr1 hz0 hz1 hne hcrit with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact lt_irrefl _ h1
  · exact lt_irrefl _ h2

/-! ### Step 4 -/

private theorem crit_unique_aux {d : ℕ} (hd : 2 ≤ d) {ε z₁ z₂ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (h10 : 0 < z₁) (h21 : z₂ < 1) (hne1 : z₁ ≠ ε) (hne2 : z₂ ≠ ε)
    (hc1 : Wr d ε z₁ = 0) (hc2 : Wr d ε z₂ = 0) (hlt : z₁ < z₂) : False := by
  have h11 : z₁ < 1 := lt_trans hlt h21
  have h20 : 0 < z₂ := lt_trans h10 hlt
  -- `ε` lies outside `[z₁, z₂]`
  have hout : ∀ x ∈ Set.Icc z₁ z₂, x ≠ ε := by
    intro x hx hxe
    subst hxe
    rcases crit_side hd hε0 hε1 h10 h11 hne1 hc1 with ⟨he1, hr1⟩ | ⟨hr1, he1⟩
    · linarith [hx.1]
    · rcases crit_side hd hε0 hε1 h20 h21 hne2 hc2 with ⟨he2, hr2⟩ | ⟨hr2, he2⟩
      · linarith
      · linarith [hx.2]
  have hmemIoo : ∀ x ∈ Set.Icc z₁ z₂, 0 < x ∧ x < 1 := fun x hx =>
    ⟨lt_of_lt_of_le h10 hx.1, lt_of_le_of_lt hx.2 h21⟩
  have hderiv : ∀ x ∈ Set.Icc z₁ z₂, HasDerivAt (fun w => Wr d ε w) (dWr d ε x) x := fun x hx =>
    hasDerivAt_Wr d ε (ne_of_gt (hmemIoo x hx).1) (ne_of_lt (hmemIoo x hx).2)
  have hcont : ContinuousOn (fun w => Wr d ε w) (Set.Icc z₁ z₂) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hdn2 : dWr d ε z₂ < 0 := dWr_neg_of_Wr_eq_zero hd hε0 hε1 h20 h21 hne2 hc2
  by_cases hle : ∀ x ∈ Set.Icc z₁ z₂, Wr d ε x ≤ 0
  · -- `Wr` stays `≤ 0`, so `z₂` is a left-approached maximum
    have hnn : (0 : ℝ) ≤ dWr d ε z₂ := by
      refine nonneg_deriv_of_le_left hlt (hderiv z₂ (Set.right_mem_Icc.mpr hlt.le))
        (fun x hx => ?_)
      rw [hc2]
      exact hle x ⟨hx.1.le, hx.2.le⟩
    linarith
  · -- `Wr` goes positive; the last zero before that has nonnegative derivative
    push Not at hle
    obtain ⟨x, hxmem, hxpos⟩ := hle
    have hx1 : z₁ < x := by
      rcases lt_or_eq_of_le hxmem.1 with h | h
      · exact h
      · exfalso; rw [← h, hc1] at hxpos; exact lt_irrefl 0 hxpos
    have hsubx : Set.Icc z₁ x ⊆ Set.Icc z₁ z₂ := Set.Icc_subset_Icc le_rfl hxmem.2
    obtain ⟨c, hcmem, hcz, hcd⟩ := exists_zero_nonneg_deriv (f := fun w => Wr d ε w)
      (f' := fun w => dWr d ε w) hx1 (hcont.mono hsubx)
      (fun y hy => hderiv y (hsubx hy)) (le_of_eq hc1) hxpos
    have hcIcc : c ∈ Set.Icc z₁ z₂ := hsubx ⟨hcmem.1, hcmem.2.le⟩
    have := dWr_neg_of_Wr_eq_zero hd hε0 hε1 (hmemIoo c hcIcc).1 (hmemIoo c hcIcc).2
      (hout c hcIcc) hcz
    linarith

/-- **Step 4 of Kenyon–Radin–Ren–Sadun, Theorem 3.3: the critical point is unique.**

`ψ_d(ε,·)` has at most one critical point off the diagonal.  Both candidates lie on the far
side of `r_*` from `ε` (`crit_side`), so `ε` does not separate them and `Wr d ε ·` is
differentiable on the interval joining them, vanishing at both ends with strictly negative
derivative at each (`dWr_neg_of_Wr_eq_zero`).  Either it stays `≤ 0`, making the right end a
maximum approached from the left — whose derivative is then `≥ 0`; or it becomes positive, and
the last zero before that has derivative `≥ 0`.  Both are impossible. -/
theorem crit_unique {d : ℕ} (hd : 2 ≤ d) {ε z₁ z₂ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (h10 : 0 < z₁) (h11 : z₁ < 1) (h20 : 0 < z₂) (h21 : z₂ < 1)
    (hne1 : z₁ ≠ ε) (hne2 : z₂ ≠ ε)
    (hc1 : Wr d ε z₁ = 0) (hc2 : Wr d ε z₂ = 0) : z₁ = z₂ := by
  rcases lt_trichotomy z₁ z₂ with hlt | heq | hgt
  · exact (crit_unique_aux hd hε0 hε1 h10 h21 hne1 hne2 hc1 hc2 hlt).elim
  · exact heq
  · exact (crit_unique_aux hd hε0 hε1 h20 h11 hne2 hne1 hc2 hc1 hgt).elim

end UpperTailOptimizers
