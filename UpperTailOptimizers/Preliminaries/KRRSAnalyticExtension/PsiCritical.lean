import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.PsiIntegral

/-!
# Step 2 with a sign: every critical point of `ψ_d(ε,·)` is a strict local maximum

Kenyon–Radin–Ren–Sadun's Step 2 shows that `ψ' = ψ'' = 0` is impossible.  What Step 4 needs is
the sharper statement *with the sign*, `ψ'' < 0`, and that is what this file proves:

  `Wr d ε z = 0  →  dWr d ε z < 0`   (`dWr_neg_of_Wr_eq_zero`).

Uniqueness of the critical point then follows at once — between two strict local maxima of a
differentiable function there has to be a local minimum — which replaces the source's Step 4.
Their own Step 4 argument takes an infimum over *real* `k` of those `k` admitting several
critical points and asserts that two of them have merged there; that merging is the content and
is not established, so it is not transcribed.

## The argument

Put `A := A(ε,z) = N'(ε,z)/D'(ε,z)` and `H(s) := N'(ε,s) - A·D'(ε,s)`, as in
`Preliminaries/KRRSAnalyticExtension/PsiIntegral.lean`.  Then `H(ε) = H(z) = 0`, criticality is `∫_ε^z H = 0`, and
`H' = D''·(R_d - A)` with `D'' > 0`.

Suppose `A ≤ R_d(z)`.  Because `R_d` rises to `r_*` and falls after it (`Preliminaries/KRRSAnalyticExtension/PsiRatio.lean`),
`{s : R_d(s) < A}` is then an *initial* segment of the interval from `ε` to `z`.  Hence for each
`s`, either `R_d ≥ A` on all of `[s,z]`, so `H` is nondecreasing there and `H(s) ≤ H(z) = 0`;
or `R_d < A` on all of `[ε,s]`, so `H` is nonincreasing there and `H(s) ≤ H(ε) = 0`.  Either
way `H ≤ 0`, and a continuous nonpositive function with vanishing integral vanishes, forcing
`R_d ≡ A` on an interval — impossible, since `R_d` is strictly monotone on each side of `r_*`.

## Contents

* `eq_zero_of_nonpos_of_integral_zero` — the calculus fact just used;
* `Rfun_lt_of_le_Rfun_right` — `{R_d < A}` is an initial segment;
* `Rfun_lt_Aavg_of_crit` — at a critical point `R_d` is below `A` at **both** endpoints;
* `dWr_neg_of_Wr_eq_zero` — Step 2 with the sign.
-/

namespace UpperTailOptimizers

open Real Set intervalIntegral

/-! ### A calculus fact -/

/-- A continuous function that is `≤ 0` on `[a,b]` and integrates to `0` vanishes on `(a,b)`. -/
theorem eq_zero_of_nonpos_of_integral_zero {H : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hcont : ContinuousOn H (Set.Icc a b)) (hnonpos : ∀ s ∈ Set.Icc a b, H s ≤ 0)
    (hint : ∫ s in a..b, H s = 0) : ∀ s ∈ Set.Ioo a b, H s = 0 := by
  intro s₀ hs₀
  by_contra hne
  have hmem : s₀ ∈ Set.Icc a b := ⟨hs₀.1.le, hs₀.2.le⟩
  have hneg : H s₀ < 0 := lt_of_le_of_ne (hnonpos s₀ hmem) hne
  have hca : ContinuousAt H s₀ := hcont.continuousAt (Icc_mem_nhds hs₀.1 hs₀.2)
  have hev : ∀ᶠ x in nhds s₀, H x < 0 := hca.eventually_lt_const hneg
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  set p : ℝ := max a (s₀ - δ / 2) with hpdef
  set q : ℝ := min b (s₀ + δ / 2) with hqdef
  have hap : a ≤ p := le_max_left _ _
  have hqb : q ≤ b := min_le_left _ _
  have hps : p < s₀ := max_lt hs₀.1 (by linarith)
  have hsq : s₀ < q := lt_min hs₀.2 (by linarith)
  have hpq : p < q := lt_trans hps hsq
  have hpb : p ≤ b := le_trans hpq.le hqb
  have haq : a ≤ q := le_trans hap hpq.le
  have hneg' : ∀ x ∈ Set.Ioo p q, 0 < -H x := by
    intro x hx
    have hx1 : s₀ - δ / 2 ≤ p := le_max_right _ _
    have hx2 : q ≤ s₀ + δ / 2 := min_le_right _ _
    have : H x < 0 := by
      refine hball ?_
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    linarith
  have hiap : IntervalIntegrable H MeasureTheory.volume a p := by
    refine ContinuousOn.intervalIntegrable (hcont.mono ?_)
    rw [Set.uIcc_of_le hap]
    exact Set.Icc_subset_Icc le_rfl hpb
  have hipq : IntervalIntegrable H MeasureTheory.volume p q := by
    refine ContinuousOn.intervalIntegrable (hcont.mono ?_)
    rw [Set.uIcc_of_le hpq.le]
    exact Set.Icc_subset_Icc hap hqb
  have hiqb : IntervalIntegrable H MeasureTheory.volume q b := by
    refine ContinuousOn.intervalIntegrable (hcont.mono ?_)
    rw [Set.uIcc_of_le hqb]
    exact Set.Icc_subset_Icc haq le_rfl
  have h1 : ∫ s in a..p, H s ≤ 0 := by
    have hnn : ∀ u ∈ Set.Icc a p, 0 ≤ -H u := fun u hu => by
      have := hnonpos u ⟨hu.1, le_trans hu.2 hpb⟩; linarith
    have h := integral_nonneg (μ := MeasureTheory.volume) (f := fun u => -H u) hap hnn
    simp only [integral_neg] at h
    linarith
  have h3 : ∫ s in q..b, H s ≤ 0 := by
    have hnn : ∀ u ∈ Set.Icc q b, 0 ≤ -H u := fun u hu => by
      have := hnonpos u ⟨le_trans haq hu.1, hu.2⟩; linarith
    have h := integral_nonneg (μ := MeasureTheory.volume) (f := fun u => -H u) hqb hnn
    simp only [integral_neg] at h
    linarith
  have h2 : ∫ s in p..q, H s < 0 := by
    have hi : IntervalIntegrable (fun s => -H s) MeasureTheory.volume p q := hipq.neg
    have h := intervalIntegral_pos_of_pos_on hi hneg' hpq
    simp only [integral_neg] at h
    linarith
  have hsum : (∫ s in a..p, H s) + (∫ s in p..q, H s) + (∫ s in q..b, H s)
      = ∫ s in a..b, H s := by
    rw [integral_add_adjacent_intervals hiap hipq,
      integral_add_adjacent_intervals (hiap.trans hipq) hiqb]
  rw [hint] at hsum
  linarith

/-! ### `{R_d < A}` is an initial segment -/

/-- If `A ≤ R_d(b)` then `R_d < A` propagates leftwards: `R_d` can only dip below `A` before
`r_*`, and it is increasing there. -/
theorem Rfun_lt_of_le_Rfun_right {d : ℕ} (hd : 2 ≤ d) {a b A : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1) (hA : A ≤ Rfun d b)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (h : Rfun d t < A) : Rfun d s < A := by
  have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
  -- `t` is below the exceptional density
  have htr : t < rStar d := by
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have := Rfun_strictAntiOn hd ⟨hcon, ht1⟩ ⟨le_trans hcon ht.2, hb1⟩ hlt
      linarith
    · rw [heq] at h; linarith
  have hsr : s ≤ rStar d := le_trans hst htr.le
  rcases lt_or_eq_of_le hst with hlt | heq
  · have := Rfun_strictMonoOn hd ⟨hs0, hsr⟩ ⟨ht0, htr.le⟩ hlt
    linarith
  · rw [heq]; exact h

/-! ### Both endpoints sit below the mean -/

/-- The `H ≤ 0` half of the argument, for the right endpoint. -/
theorem Hfun_nonpos_right {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hab : a < b) (hne : b ≠ a) (hA : Aavg d a b ≤ Rfun d b) :
    ∀ s ∈ Set.Icc a b, Hfun d a b s ≤ 0 := by
  have hb0 : 0 < b := lt_trans ha0 hab
  have ha1 : a < 1 := lt_trans hab hb1
  have hsubIoo : ∀ s ∈ Set.Icc a b, 0 < s ∧ s < 1 := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hb1⟩
  have hderiv : ∀ s ∈ Set.Icc a b,
      HasDerivAt (Hfun d a b) (d2D d s * (Rfun d s - Aavg d a b)) s := fun s hs =>
    hasDerivAt_Hfun hd a b (hsubIoo s hs).1 (hsubIoo s hs).2
  have hcontAll : ContinuousOn (Hfun d a b) (Set.Icc a b) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  intro s hs
  by_cases hRs : Rfun d s < Aavg d a b
  · -- `H` is nonincreasing on `[a,s]`, and `H a = 0`
    have hsub : Set.Icc a s ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hs.2
    have hanti : AntitoneOn (Hfun d a b) (Set.Icc a s) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc a s) (hcontAll.mono hsub)
        (fun x hx => ((hderiv x (hsub (interior_subset hx))).differentiableAt).differentiableWithinAt)
        (fun x hx => ?_)
      rw [interior_Icc] at hx
      have hxmem : x ∈ Set.Icc a b := hsub ⟨hx.1.le, hx.2.le⟩
      rw [(hderiv x hxmem).deriv]
      have hlt : Rfun d x < Aavg d a b :=
        Rfun_lt_of_le_Rfun_right hd ha0 hb1 hA hxmem (hsub ⟨hs.1, le_rfl⟩) hx.2.le hRs
      have hpos : 0 < d2D d x := d2D_pos hd (hsubIoo x hxmem).1
      nlinarith [hpos, hlt]
    have := hanti (Set.left_mem_Icc.mpr hs.1) (Set.right_mem_Icc.mpr hs.1) hs.1
    rw [Hfun_left] at this
    exact this
  · -- `H` is nondecreasing on `[s,b]`, and `H b = 0`
    push Not at hRs
    have hsub : Set.Icc s b ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 le_rfl
    have hmono : MonotoneOn (Hfun d a b) (Set.Icc s b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc s b) (hcontAll.mono hsub)
        (fun x hx => ((hderiv x (hsub (interior_subset hx))).differentiableAt).differentiableWithinAt)
        (fun x hx => ?_)
      rw [interior_Icc] at hx
      have hxmem : x ∈ Set.Icc a b := hsub ⟨hx.1.le, hx.2.le⟩
      rw [(hderiv x hxmem).deriv]
      have hge : Aavg d a b ≤ Rfun d x := by
        by_contra hcon
        push Not at hcon
        have := Rfun_lt_of_le_Rfun_right hd ha0 hb1 hA (hsub ⟨le_rfl, hs.2⟩) hxmem hx.1.le hcon
        linarith
      have hpos : 0 < d2D d x := d2D_pos hd (hsubIoo x hxmem).1
      nlinarith [hpos, hge]
    have := hmono (Set.left_mem_Icc.mpr hs.2) (Set.right_mem_Icc.mpr hs.2) hs.2
    rw [Hfun_right hd ha0 hb0 hne] at this
    exact this

/-- The `≥ 0` companion of `eq_zero_of_nonpos_of_integral_zero`. -/
theorem eq_zero_of_nonneg_of_integral_zero {H : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn H (Set.Icc a b)) (hnonneg : ∀ s ∈ Set.Icc a b, 0 ≤ H s)
    (hint : ∫ s in a..b, H s = 0) : ∀ s ∈ Set.Ioo a b, H s = 0 := by
  have hcont' : ContinuousOn (fun s => -H s) (Set.Icc a b) := hcont.neg
  have hnonpos : ∀ s ∈ Set.Icc a b, -H s ≤ 0 := fun s hs => by
    have := hnonneg s hs; linarith
  have hint' : ∫ s in a..b, -H s = 0 := by
    simp only [integral_neg, hint, neg_zero]
  intro s hs
  have := eq_zero_of_nonpos_of_integral_zero hab hcont' hnonpos hint' s hs
  linarith

/-- The mirror of `Rfun_lt_of_le_Rfun_right`: if `A ≤ R_d(a)` then `R_d < A` propagates
rightwards. -/
theorem Rfun_lt_of_le_Rfun_left {d : ℕ} (hd : 2 ≤ d) {a b A : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1) (hA : A ≤ Rfun d a)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (h : Rfun d s < A) : Rfun d t < A := by
  have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 hb1
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
  have hsr : rStar d < s := by
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le hs.1 with hlt | heq
    · have := Rfun_strictMonoOn hd ⟨ha0, le_trans hs.1 hcon⟩ ⟨hs0, hcon⟩ hlt
      linarith
    · rw [← heq] at h; linarith
  have htr : rStar d ≤ t := le_trans hsr.le hst
  rcases lt_or_eq_of_le hst with hlt | heq
  · have := Rfun_strictAntiOn hd ⟨hsr.le, hs1⟩ ⟨htr, ht1⟩ hlt
    linarith
  · rw [← heq]; exact h

/-- The `H ≥ 0` half of the argument, for the left endpoint. -/
theorem Hfun_nonneg_left {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hab : a < b) (hne : b ≠ a) (hA : Aavg d a b ≤ Rfun d a) :
    ∀ s ∈ Set.Icc a b, 0 ≤ Hfun d a b s := by
  have hb0 : 0 < b := lt_trans ha0 hab
  have hsubIoo : ∀ s ∈ Set.Icc a b, 0 < s ∧ s < 1 := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hb1⟩
  have hderiv : ∀ s ∈ Set.Icc a b,
      HasDerivAt (Hfun d a b) (d2D d s * (Rfun d s - Aavg d a b)) s := fun s hs =>
    hasDerivAt_Hfun hd a b (hsubIoo s hs).1 (hsubIoo s hs).2
  have hcontAll : ContinuousOn (Hfun d a b) (Set.Icc a b) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  intro s hs
  by_cases hRs : Rfun d s < Aavg d a b
  · -- `H` is nonincreasing on `[s,b]`, and `H b = 0`
    have hsub : Set.Icc s b ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 le_rfl
    have hanti : AntitoneOn (Hfun d a b) (Set.Icc s b) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc s b) (hcontAll.mono hsub)
        (fun x hx =>
          ((hderiv x (hsub (interior_subset hx))).differentiableAt).differentiableWithinAt)
        (fun x hx => ?_)
      rw [interior_Icc] at hx
      have hxmem : x ∈ Set.Icc a b := hsub ⟨hx.1.le, hx.2.le⟩
      rw [(hderiv x hxmem).deriv]
      have hlt : Rfun d x < Aavg d a b :=
        Rfun_lt_of_le_Rfun_left hd ha0 hb1 hA (hsub ⟨le_rfl, hs.2⟩) hxmem hx.1.le hRs
      have hpos : 0 < d2D d x := d2D_pos hd (hsubIoo x hxmem).1
      nlinarith [hpos, hlt]
    have := hanti (Set.left_mem_Icc.mpr hs.2) (Set.right_mem_Icc.mpr hs.2) hs.2
    rw [Hfun_right hd ha0 hb0 hne] at this
    exact this
  · -- `H` is nondecreasing on `[a,s]`, and `H a = 0`
    push Not at hRs
    have hsub : Set.Icc a s ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hs.2
    have hmono : MonotoneOn (Hfun d a b) (Set.Icc a s) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc a s) (hcontAll.mono hsub)
        (fun x hx =>
          ((hderiv x (hsub (interior_subset hx))).differentiableAt).differentiableWithinAt)
        (fun x hx => ?_)
      rw [interior_Icc] at hx
      have hxmem : x ∈ Set.Icc a b := hsub ⟨hx.1.le, hx.2.le⟩
      rw [(hderiv x hxmem).deriv]
      have hge : Aavg d a b ≤ Rfun d x := by
        by_contra hcon
        push Not at hcon
        have := Rfun_lt_of_le_Rfun_left hd ha0 hb1 hA hxmem (hsub ⟨hs.1, le_rfl⟩) hx.2.le hcon
        linarith
      have hpos : 0 < d2D d x := d2D_pos hd (hsubIoo x hxmem).1
      nlinarith [hpos, hge]
    have := hmono (Set.left_mem_Icc.mpr hs.1) (Set.right_mem_Icc.mpr hs.1) hs.1
    rw [Hfun_left] at this
    exact this

/-- `R_d` is not constant on any nondegenerate subinterval of `(0,1)`: it is strictly monotone
on each side of `r_*`. -/
theorem not_Rfun_const {d : ℕ} (hd : 2 ≤ d) {a b A : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hab : a < b) (h : ∀ s ∈ Set.Ioo a b, Rfun d s = A) : False := by
  by_cases hcase : rStar d ≤ a
  · set s₁ : ℝ := a + (b - a) / 3 with hs₁
    set s₂ : ℝ := a + 2 * (b - a) / 3 with hs₂
    have h₁ : s₁ ∈ Set.Ioo a b := ⟨by rw [hs₁]; linarith, by rw [hs₁]; linarith⟩
    have h₂ : s₂ ∈ Set.Ioo a b := ⟨by rw [hs₂]; linarith, by rw [hs₂]; linarith⟩
    have hlt : s₁ < s₂ := by rw [hs₁, hs₂]; linarith
    have := Rfun_strictAntiOn hd
      ⟨le_trans hcase h₁.1.le, lt_trans h₁.2 hb1⟩ ⟨le_trans hcase h₂.1.le, lt_trans h₂.2 hb1⟩ hlt
    rw [h s₁ h₁, h s₂ h₂] at this
    exact lt_irrefl A this
  · push Not at hcase
    set u : ℝ := min b (rStar d) with hu
    have hau : a < u := lt_min hab hcase
    have hub : u ≤ b := min_le_left _ _
    have hur : u ≤ rStar d := min_le_right _ _
    set s₁ : ℝ := a + (u - a) / 3 with hs₁
    set s₂ : ℝ := a + 2 * (u - a) / 3 with hs₂
    have h₁ : s₁ ∈ Set.Ioo a b :=
      ⟨by rw [hs₁]; linarith, by rw [hs₁]; linarith [hub]⟩
    have h₂ : s₂ ∈ Set.Ioo a b :=
      ⟨by rw [hs₂]; linarith, by rw [hs₂]; linarith [hub]⟩
    have hlt : s₁ < s₂ := by rw [hs₁, hs₂]; linarith
    have hr₁ : s₁ ≤ rStar d := by rw [hs₁]; linarith [hur]
    have hr₂ : s₂ ≤ rStar d := by rw [hs₂]; linarith [hur]
    have := Rfun_strictMonoOn hd ⟨lt_trans ha0 h₁.1, hr₁⟩ ⟨lt_trans ha0 h₂.1, hr₂⟩ hlt
    rw [h s₁ h₁, h s₂ h₂] at this
    exact lt_irrefl A this

/-- **At a critical point the ratio `R_d` lies strictly below the mean `A` at both endpoints.**
This is Step 2 of the source, with the sign that Step 4 needs. -/
theorem Rfun_lt_Aavg_of_crit {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hab : a < b) (hcrit : Wr d a b = 0) :
    Rfun d a < Aavg d a b ∧ Rfun d b < Aavg d a b := by
  have hb0 : 0 < b := lt_trans ha0 hab
  have ha1 : a < 1 := lt_trans hab hb1
  have hne : b ≠ a := ne_of_gt hab
  have hsubIoo : ∀ s ∈ Set.Icc a b, 0 < s ∧ s < 1 := fun s hs =>
    ⟨lt_of_lt_of_le ha0 hs.1, lt_of_le_of_lt hs.2 hb1⟩
  have hderiv : ∀ s ∈ Set.Icc a b,
      HasDerivAt (Hfun d a b) (d2D d s * (Rfun d s - Aavg d a b)) s := fun s hs =>
    hasDerivAt_Hfun hd a b (hsubIoo s hs).1 (hsubIoo s hs).2
  have hcontAll : ContinuousOn (Hfun d a b) (Set.Icc a b) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  have hint : ∫ s in a..b, Hfun d a b s = 0 :=
    integral_Hfun_eq_zero_of_Wr hd ha0 ha1 hb0 hb1 hne hcrit
  -- from `H ≡ 0` on the interior, `R_d` would be constant there
  have hcontra : (∀ s ∈ Set.Ioo a b, Hfun d a b s = 0) → False := by
    intro hz
    refine not_Rfun_const hd ha0 hb1 hab (A := Aavg d a b) (fun s hs => ?_)
    have hev : Hfun d a b =ᶠ[nhds s] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht using hz t ht
    have h0 : HasDerivAt (Hfun d a b) 0 s :=
      (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev
    have h1 := hderiv s ⟨hs.1.le, hs.2.le⟩
    have hzero : (0 : ℝ) = d2D d s * (Rfun d s - Aavg d a b) := h0.unique h1
    have hpos : 0 < d2D d s := d2D_pos hd (hsubIoo s ⟨hs.1.le, hs.2.le⟩).1
    have : Rfun d s - Aavg d a b = 0 := by
      rcases mul_eq_zero.mp hzero.symm with h' | h'
      · exact absurd h' (ne_of_gt hpos)
      · exact h'
    linarith
  constructor
  · by_contra hcon
    push Not at hcon
    exact hcontra (eq_zero_of_nonneg_of_integral_zero hab hcontAll
      (Hfun_nonneg_left hd ha0 hb1 hab hne hcon) hint)
  · by_contra hcon
    push Not at hcon
    exact hcontra (eq_zero_of_nonpos_of_integral_zero hab hcontAll
      (Hfun_nonpos_right hd ha0 hb1 hab hne hcon) hint)

/-- **Step 2 with the sign.**  Every off-diagonal critical point of `ψ_d(ε,·)` is a strict local
maximum: `Wr = 0` forces `dWr < 0`. -/
theorem dWr_neg_of_Wr_eq_zero {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hne : z ≠ ε) (hcrit : Wr d ε z = 0) : dWr d ε z < 0 := by
  have hDne := dD_ne_zero hd hε0 hz0 hne
  have hDpos : 0 < Dfun d ε z := Dfun_pos hd hε0 hz0.le hne
  have h2Dpos : 0 < d2D d z := d2D_pos hd hz0
  -- `R_d(z) < A(ε,z)`, in either orientation
  have hR : Rfun d z < Aavg d ε z := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `z < ε`: apply the two-endpoint lemma to `(z, ε)` and take the left endpoint
      have hcrit' : Wr d z ε = 0 := Wr_eq_zero_swap hcrit
      have := (Rfun_lt_Aavg_of_crit hd hz0 hε1 hlt hcrit').1
      rwa [Aavg_symm] at this
    · exact (Rfun_lt_Aavg_of_crit hd hε0 hz1 hgt hcrit).2
  -- `dWr = D·D''·(R_d(z) - A)` at a critical point
  have hN : Nfun ε z = Aavg d ε z * Dfun d ε z := by
    unfold Aavg
    have hW : dN ε z * Dfun d ε z - Nfun ε z * dD d ε z = 0 := hcrit
    field_simp
    linarith [hW]
  have hd2N : d2N z = Rfun d z * d2D d z := by
    unfold Rfun
    field_simp
  have hval : dWr d ε z = Dfun d ε z * d2D d z * (Rfun d z - Aavg d ε z) := by
    unfold dWr
    rw [hN, hd2N]; ring
  rw [hval]
  have : Rfun d z - Aavg d ε z < 0 := by linarith
  have hprod : 0 < Dfun d ε z * d2D d z := mul_pos hDpos h2Dpos
  exact mul_neg_of_pos_of_neg hprod this

end UpperTailOptimizers
