import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Reduced

/-!
# Nondegeneracy of the scalar KRR–S maximizer

This file formalises paragraph 1 ("Nondegeneracy of the scalar maximizer") of Appendix B of
`paper/paper.tex`, whose conclusion is `eq:krrs-scalar-nondegeneracy`,
`∂_z²ψ_d(ε₀,z₀) < 0`.

Since `ψ_d(ε,z) = 𝒩_ε(z)/𝒟_ε(z)` (`eq:krrs-entropy-remainder`, `eq:krrs-moment-remainder`) has a denominator that
vanishes at `z = ε`, we record the statement in the quotient-free form that is used
downstream: with

* `Wr d ε z  = 𝒩'_ε(z)𝒟_ε(z) - 𝒩_ε(z)𝒟'_ε(z)`, the numerator of `∂_zψ_d`, and
* `dWr d ε z = 𝒩''_ε(z)𝒟_ε(z) - 𝒩_ε(z)𝒟''_ε(z)`, its `z`-derivative,

an interior maximizer `z` of `ψ_d(ε,·)` with `z ≠ ε` satisfies `Wr d ε z = 0` and
`dWr d ε z < 0` (`krrs_scalar_nondegenerate`).  Dividing by `𝒟_ε(z)² > 0` and
`𝒟_ε(z) > 0` respectively turns these into `∂_zψ_d = 0` and `∂_z²ψ_d < 0`.

## Method

The appendix applies the interior-maximum argument to `ψ_d(ε₀,·)` itself ("an interior local
maximum cannot have a first nonzero derivative of odd order") and then differentiates the
identity `𝒩_{ε₀} = ψ_d(ε₀,·)𝒟_{ε₀}` to obtain `eq:krrs-ratio-derivatives`.  To avoid the
quotient, the argument is run here on the *auxiliary* function

  `h(w) = 𝒩_ε(w) - λ𝒟_ε(w)`,  `λ := ψ_d(ε,z)`,

which is `≤ 0` on all of `(0,1)` (including at `w = ε`, where both `𝒩` and `𝒟` vanish)
and `= 0` at `w = z`.  So `h` has an interior maximum at `z`, hence `h'(z) = 0` and
`h''(z) ≤ 0`; and if `h''(z) = 0` then `h'''(z) = 0`, since a first nonvanishing
derivative of odd order at an interior point forces `h` to exceed `h(z)` on one side.
The equations `h''(z) = 0` and `h'''(z) = 0` are the two identities of
`eq:krrs-ratio-derivatives`, and together they force `z = (d-1)/d = r_*`, which is
excluded by hypothesis.  (The paper goes on to derive `ε₀ = (d-1)/d` from `z₀ = ε_*`;
`krrs_family_exists` discharges the hypothesis by that argument, via the involution.)

The calculus is isolated in the private lemma `localmax_derivs`, and the "positive
derivative pushes the value up on the right and down on the left" step — used four
times — in `exists_sides_pos` / `exists_sides_neg`.
-/

namespace UpperTailOptimizers

open Real Filter Topology

/-! ### Two calculus helpers -/

/-- If `f` has derivative `v` at `x`, then the slope of `f` at `x` eventually inherits any
neighbourhood property of `v`.  Metric form, for later use with explicit intervals. -/
private theorem exists_slope_nbhd {f : ℝ → ℝ} {v x : ℝ} (hf : HasDerivAt f v x)
    {p : ℝ → Prop} (hp : ∀ᶠ u in 𝓝 v, p u) :
    ∃ δ > 0, ∀ w, w ≠ x → |w - x| < δ → p (_root_.slope f x w) := by
  have hs : Tendsto (_root_.slope f x) (𝓝[≠] x) (𝓝 v) := hasDerivAt_iff_tendsto_slope.mp hf
  have h1 : ∀ᶠ w in 𝓝[≠] x, p (_root_.slope f x w) := hs.eventually hp
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨δ, hδ, hmem⟩ := h1
  refine ⟨δ, hδ, fun w hw hd => hmem ?_ ?_⟩
  · rwa [Real.dist_eq]
  · simpa using hw

/-- A strictly positive derivative at `x` makes `f` bigger immediately to the right of `x`
and smaller immediately to the left. -/
private theorem exists_sides_pos {f : ℝ → ℝ} {v x : ℝ} (hf : HasDerivAt f v x)
    (hv : 0 < v) : ∃ δ > 0, (∀ w, x < w → w < x + δ → f x < f w) ∧
      (∀ w, x - δ < w → w < x → f w < f x) := by
  obtain ⟨δ, hδ, hmem⟩ := exists_slope_nbhd hf (eventually_gt_nhds hv)
  refine ⟨δ, hδ, fun w hw1 hw2 => ?_, fun w hw1 hw2 => ?_⟩
  · refine (slope_pos_iff_of_le hw1.le).mp (hmem w (ne_of_gt hw1) ?_)
    rw [abs_of_pos (by linarith : (0:ℝ) < w - x)]; linarith
  · have h : 0 < _root_.slope f x w := by
      refine hmem w (ne_of_lt hw2) ?_
      rw [abs_of_neg (by linarith : w - x < 0)]; linarith
    rw [slope_comm] at h
    exact (slope_pos_iff_of_le hw2.le).mp h

/-- A strictly negative derivative at `x` makes `f` smaller immediately to the right of `x`
and bigger immediately to the left. -/
private theorem exists_sides_neg {f : ℝ → ℝ} {v x : ℝ} (hf : HasDerivAt f v x)
    (hv : v < 0) : ∃ δ > 0, (∀ w, x < w → w < x + δ → f w < f x) ∧
      (∀ w, x - δ < w → w < x → f x < f w) := by
  obtain ⟨δ, hδ, hmem⟩ := exists_slope_nbhd hf (eventually_lt_nhds hv)
  refine ⟨δ, hδ, fun w hw1 hw2 => ?_, fun w hw1 hw2 => ?_⟩
  · refine (slope_neg_iff_of_le hw1.le).mp (hmem w (ne_of_gt hw1) ?_)
    rw [abs_of_pos (by linarith : (0:ℝ) < w - x)]; linarith
  · have h : _root_.slope f x w < 0 := by
      refine hmem w (ne_of_lt hw2) ?_
      rw [abs_of_neg (by linarith : w - x < 0)]; linarith
    rw [slope_comm] at h
    exact (slope_neg_iff_of_le hw2.le).mp h

/-- Mean value form: a pointwise-positive derivative on `[x,y]` makes `f x < f y`. -/
private theorem lt_of_hasDerivAt_pos {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hd : ∀ w ∈ Set.Icc x y, HasDerivAt f (f' w) w)
    (hp : ∀ w ∈ Set.Ioo x y, 0 < f' w) : f x < f y := by
  have hcont : ContinuousOn f (Set.Icc x y) := fun w hw =>
    (hd w hw).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Set.Icc x y) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc x y) hcont ?_
    intro w hw
    rw [interior_Icc] at hw
    rw [(hd w (Set.Ioo_subset_Icc_self hw)).deriv]
    exact hp w hw
  exact hmono (Set.left_mem_Icc.mpr hxy.le) (Set.right_mem_Icc.mpr hxy.le) hxy

/-- Mean value form: a pointwise-negative derivative on `[x,y]` makes `f y < f x`. -/
private theorem lt_of_hasDerivAt_neg {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hd : ∀ w ∈ Set.Icc x y, HasDerivAt f (f' w) w)
    (hp : ∀ w ∈ Set.Ioo x y, f' w < 0) : f y < f x := by
  have hcont : ContinuousOn f (Set.Icc x y) := fun w hw =>
    (hd w hw).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f (Set.Icc x y) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc x y) hcont ?_
    intro w hw
    rw [interior_Icc] at hw
    rw [(hd w (Set.Ioo_subset_Icc_self hw)).deriv]
    exact hp w hw
  exact hanti (Set.left_mem_Icc.mpr hxy.le) (Set.right_mem_Icc.mpr hxy.le) hxy

/-- **The calculus core of Appendix B, paragraph 1.**  If `f` attains its maximum over an
open interval at an interior point `x`, and `f₁, f₂, f₃` are its first three derivatives
there, then `f₁(x) = 0`, `f₂(x) ≤ 0`, and — the paper's "an interior local maximum cannot
have a first nonzero derivative of odd order" step — `f₂(x) = 0` forces `f₃(x) = 0`. -/
private theorem localmax_derivs {f f₁ f₂ f₃ : ℝ → ℝ} {A B x : ℝ}
    (hx : x ∈ Set.Ioo A B)
    (hD1 : ∀ w ∈ Set.Ioo A B, HasDerivAt f (f₁ w) w)
    (hD2 : ∀ w ∈ Set.Ioo A B, HasDerivAt f₁ (f₂ w) w)
    (hD3 : ∀ w ∈ Set.Ioo A B, HasDerivAt f₂ (f₃ w) w)
    (hM : ∀ w ∈ Set.Ioo A B, f w ≤ f x) :
    f₁ x = 0 ∧ f₂ x ≤ 0 ∧ (f₂ x = 0 → f₃ x = 0) := by
  have hA : A < x := hx.1
  have hB : x < B := hx.2
  have hlocmax : IsLocalMax f x := by
    filter_upwards [Ioo_mem_nhds hA hB] with w hw
    exact hM w hw
  have h1 : f₁ x = 0 := hlocmax.hasDerivAt_eq_zero (hD1 x hx)
  -- the second derivative is nonpositive.
  have h2 : f₂ x ≤ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨δ, hδ, hright, -⟩ := exists_sides_pos (hD2 x hx) hcon
    obtain ⟨y, hxy, hyB, hyδ⟩ : ∃ y, x < y ∧ y < B ∧ y < x + δ := by
      have hm1 : min δ (B - x) ≤ δ := min_le_left _ _
      have hm2 : min δ (B - x) ≤ B - x := min_le_right _ _
      have hmpos : 0 < min δ (B - x) := lt_min hδ (by linarith)
      exact ⟨x + min δ (B - x) / 2, by linarith, by linarith, by linarith⟩
    have hsub : ∀ w ∈ Set.Icc x y, w ∈ Set.Ioo A B := fun w hw =>
      ⟨lt_of_lt_of_le hA hw.1, lt_of_le_of_lt hw.2 hyB⟩
    have hfy : f x < f y :=
      lt_of_hasDerivAt_pos hxy (fun w hw => hD1 w (hsub w hw)) (fun w hw => by
        have := hright w hw.1 (by linarith [hw.2]); linarith)
    have := hM y ⟨by linarith, hyB⟩
    linarith
  refine ⟨h1, h2, ?_⟩
  -- a vanishing second derivative forces a vanishing third derivative.
  intro h2z
  by_contra hcon
  rcases lt_or_gt_of_ne (hcon : f₃ x ≠ 0) with hneg | hpos
  · -- `f₃ x < 0`: then `f₂ > 0`, hence `f₁ < 0`, hence `f` decreasing, just left of `x`.
    obtain ⟨δ, hδ, -, hleft⟩ := exists_sides_neg (hD3 x hx) hneg
    obtain ⟨y, hyx, hAy, hyδ⟩ : ∃ y, y < x ∧ A < y ∧ x - δ < y := by
      have hm1 : min δ (x - A) ≤ δ := min_le_left _ _
      have hm2 : min δ (x - A) ≤ x - A := min_le_right _ _
      have hmpos : 0 < min δ (x - A) := lt_min hδ (by linarith)
      exact ⟨x - min δ (x - A) / 2, by linarith, by linarith, by linarith⟩
    have hsub : ∀ w ∈ Set.Icc y x, w ∈ Set.Ioo A B := fun w hw =>
      ⟨lt_of_lt_of_le hAy hw.1, lt_of_le_of_lt hw.2 hB⟩
    have hf2 : ∀ w ∈ Set.Ioo y x, 0 < f₂ w := fun w hw => by
      have := hleft w (by linarith [hw.1]) hw.2; linarith
    have hf1 : ∀ w ∈ Set.Ioo y x, f₁ w < 0 := by
      intro w hw
      have hsub' : ∀ u ∈ Set.Icc w x, u ∈ Set.Ioo A B := fun u hu =>
        ⟨lt_of_lt_of_le (lt_trans hAy hw.1) hu.1, lt_of_le_of_lt hu.2 hB⟩
      have := lt_of_hasDerivAt_pos hw.2 (fun u hu => hD2 u (hsub' u hu))
        (fun u hu => hf2 u ⟨lt_trans hw.1 hu.1, hu.2⟩)
      linarith
    have hfy : f x < f y := lt_of_hasDerivAt_neg hyx (fun w hw => hD1 w (hsub w hw)) hf1
    have := hM y ⟨hAy, by linarith⟩
    linarith
  · -- `0 < f₃ x`: then `f₂ > 0`, hence `f₁ > 0`, hence `f` increasing, just right of `x`.
    obtain ⟨δ, hδ, hright, -⟩ := exists_sides_pos (hD3 x hx) hpos
    obtain ⟨y, hxy, hyB, hyδ⟩ : ∃ y, x < y ∧ y < B ∧ y < x + δ := by
      have hm1 : min δ (B - x) ≤ δ := min_le_left _ _
      have hm2 : min δ (B - x) ≤ B - x := min_le_right _ _
      have hmpos : 0 < min δ (B - x) := lt_min hδ (by linarith)
      exact ⟨x + min δ (B - x) / 2, by linarith, by linarith, by linarith⟩
    have hsub : ∀ w ∈ Set.Icc x y, w ∈ Set.Ioo A B := fun w hw =>
      ⟨lt_of_lt_of_le hA hw.1, lt_of_le_of_lt hw.2 hyB⟩
    have hf2 : ∀ w ∈ Set.Ioo x y, 0 < f₂ w := fun w hw => by
      have := hright w hw.1 (by linarith [hw.2]); linarith
    have hf1 : ∀ w ∈ Set.Ioo x y, 0 < f₁ w := by
      intro w hw
      have hsub' : ∀ u ∈ Set.Icc x w, u ∈ Set.Ioo A B := fun u hu =>
        ⟨lt_of_lt_of_le hA hu.1, lt_of_le_of_lt (le_trans hu.2 hw.2.le) hyB⟩
      have := lt_of_hasDerivAt_pos hw.1 (fun u hu => hD2 u (hsub' u hu))
        (fun u hu => hf2 u ⟨hu.1, lt_trans hu.2 hw.2⟩)
      linarith
    have hfy : f x < f y := lt_of_hasDerivAt_pos hxy (fun w hw => hD1 w (hsub w hw)) hf1
    have := hM y ⟨by linarith, hyB⟩
    linarith

/-! ### The numerator of `∂_zψ_d` -/

/-- `Wr` is the numerator of the `z`-derivative of `ψ_d`: `∂_z(𝒩/𝒟) = Wr/𝒟²`. -/
noncomputable def Wr (d : ℕ) (ε z : ℝ) : ℝ := dN ε z * Dfun d ε z - Nfun ε z * dD d ε z

/-- The `z`-derivative of `Wr`; the cross terms cancel. -/
noncomputable def dWr (d : ℕ) (ε z : ℝ) : ℝ := d2N z * Dfun d ε z - Nfun ε z * d2D d z

/-- `𝒟'' ` is the derivative of `𝒟'` for *every* `d`, not just `d ≥ 2`: for `d ≤ 1` both
`𝒟'` and `𝒟''` vanish identically because of the factor `d(d-1)`. -/
private theorem hasDerivAt_dD_all (d : ℕ) (ε z : ℝ) :
    HasDerivAt (fun x => dD d ε x) (d2D d z) z := by
  rcases Nat.lt_or_ge d 2 with hlt | hge
  · interval_cases d
    · simpa [dD, d2D] using hasDerivAt_const z (0 : ℝ)
    · simpa [dD, d2D] using hasDerivAt_const z (0 : ℝ)
  · exact hasDerivAt_dD hge ε z

/-- The derivative of `Wr` is `dWr`. -/
theorem hasDerivAt_Wr (d : ℕ) (ε : ℝ) {z : ℝ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    HasDerivAt (fun w => Wr d ε w) (dWr d ε z) z := by
  have hN := hasDerivAt_Nfun ε h0 h1
  have hD := hasDerivAt_Dfun d ε z
  have hdN := hasDerivAt_dN ε h0 h1
  have hdD := hasDerivAt_dD_all d ε z
  have h := (hdN.mul hD).sub (hN.mul hdD)
  have hfun : (fun w => Wr d ε w)
      = fun w => dN ε w * Dfun d ε w - Nfun ε w * dD d ε w := rfl
  rw [hfun]
  convert h using 1
  all_goals try rfl
  unfold dWr
  ring

/-! ### The nondegeneracy statement -/

/-- **Appendix B, paragraph 1** `eq:krrs-scalar-nondegeneracy`, in the quotient-free form
used downstream: at an interior maximizer `z ≠ ε` of `ψ_d(ε,·)` which is not the
exceptional density `r_* = (d-1)/d`, the numerator `Wr` of `∂_zψ_d` vanishes and its
derivative `dWr` is strictly negative.  Dividing by `𝒟_ε(z)^2 > 0` and `𝒟_ε(z) > 0` gives
`∂_zψ_d(ε,z) = 0` and `∂_z²ψ_d(ε,z) < 0`. -/
theorem krrs_scalar_nondegenerate {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ}
    (hε0 : 0 < ε) (hz0 : 0 < z) (hz1 : z < 1)
    (hne : z ≠ ε) (hstar : z ≠ rStar d)
    (hmax : ∀ w, 0 < w → w < 1 → w ≠ ε → psiD d ε w ≤ psiD d ε z) :
    Wr d ε z = 0 ∧ dWr d ε z < 0 := by
  have hzne : z ≠ 0 := ne_of_gt hz0
  have h1z : (0:ℝ) < 1 - z := by linarith
  have h1zne : (1:ℝ) - z ≠ 0 := ne_of_gt h1z
  have hDz : 0 < Dfun d ε z := Dfun_pos hd hε0 hz0.le hne
  have hDne : Dfun d ε z ≠ 0 := ne_of_gt hDz
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = psiD d ε z := ⟨_, rfl⟩
  have hlamD : lam * Dfun d ε z = Nfun ε z := by
    rw [hlam]; unfold psiD; field_simp
  -- the auxiliary function `h(w) = 𝒩(w) - λ𝒟(w)` is `≤ 0` on `(0,1)`, with
  -- value `0` at `z`.
  have hfz : Nfun ε z - lam * Dfun d ε z = 0 := by rw [hlamD]; ring
  have hM : ∀ w ∈ Set.Ioo (0:ℝ) 1,
      Nfun ε w - lam * Dfun d ε w ≤ Nfun ε z - lam * Dfun d ε z := by
    intro w hw
    rw [hfz]
    by_cases hwe : w = ε
    · subst hwe
      have hN : Nfun w w = 0 := by unfold Nfun; ring
      have hD : Dfun d w w = 0 := by unfold Dfun; ring
      rw [hN, hD]; simp
    · have hDw : 0 < Dfun d ε w := Dfun_pos hd hε0 (le_of_lt hw.1) hwe
      have hmx := hmax w hw.1 hw.2 hwe
      rw [← hlam] at hmx
      simp only [psiD] at hmx
      rw [div_le_iff₀ hDw] at hmx
      linarith
  -- the calculus core `localmax_derivs`, applied to `h`.
  obtain ⟨e1, e2, e3⟩ := localmax_derivs (A := 0) (B := 1) (x := z)
    (f := fun w => Nfun ε w - lam * Dfun d ε w)
    (f₁ := fun w => dN ε w - lam * dD d ε w)
    (f₂ := fun w => d2N w - lam * d2D d w)
    (f₃ := fun w => d3N w - lam * d3D d w)
    ⟨hz0, hz1⟩
    (fun w hw => (hasDerivAt_Nfun ε (ne_of_gt hw.1) (ne_of_lt hw.2)).sub
      ((hasDerivAt_Dfun d ε w).const_mul lam))
    (fun w hw => (hasDerivAt_dN ε (ne_of_gt hw.1) (ne_of_lt hw.2)).sub
      ((hasDerivAt_dD hd ε w).const_mul lam))
    (fun w hw => (hasDerivAt_d2N (ne_of_gt hw.1) (ne_of_lt hw.2)).sub
      ((hasDerivAt_d2D hd w).const_mul lam))
    hM
  have E1 : dN ε z - lam * dD d ε z = 0 := e1
  have E2 : d2N z - lam * d2D d z ≤ 0 := e2
  have E3 : d2N z - lam * d2D d z = 0 → d3N z - lam * d3D d z = 0 := e3
  refine ⟨?_, ?_⟩
  · -- the critical-point identity `Wr = 0`.
    unfold Wr
    have hdn : dN ε z = lam * dD d ε z := by linarith
    rw [hdn, ← hlamD]
    ring
  · -- `dWr ≤ 0`; and `dWr = 0` would give both identities of `eq:krrs-ratio-derivatives`,
    -- forcing `z = r_*`.
    have hfac : dWr d ε z = Dfun d ε z * (d2N z - lam * d2D d z) := by
      unfold dWr; rw [← hlamD]; ring
    have hle : dWr d ε z ≤ 0 := by rw [hfac]; nlinarith
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      rw [hfac] at heq
      have hii0 : d2N z - lam * d2D d z = 0 := by
        rcases mul_eq_zero.mp heq with h' | h'
        · exact absurd h' hDne
        · exact h'
      have hii : d2N z = lam * d2D d z := by linarith
      have hiii : d3N z = lam * d3D d z := by have := E3 hii0; linarith
      rcases Nat.lt_or_ge d 3 with hlt3 | hge3
      · -- `d = 2`: `𝒟''' ≡ 0`, so `𝒩'''(z) = 0`, i.e. `z = 1/2 = r_*`.
        have hd2 : d = 2 := by omega
        subst hd2
        have h3D : d3D 2 z = 0 := by unfold d3D; norm_num
        rw [h3D, mul_zero] at hiii
        unfold d3N at hiii
        field_simp at hiii
        refine hstar ?_
        unfold rStar
        norm_num
        linarith
      · -- `d ≥ 3`: divide `𝒩''' = λ𝒟'''` by `𝒩'' = λ𝒟''`.
        have hK3 : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hge3
        have hcross : d3N z * d2D d z = d2N z * d3D d z := by rw [hii, hiii]; ring
        have hAid : d3N z * (z ^ 2 * (1 - z) ^ 2) = 1 - 2 * z := by
          unfold d3N; field_simp
        have hBid : d2N z * (z * (1 - z)) = -1 := by
          unfold d2N; field_simp
        have hstep : (1 - 2 * z) * d2D d z = -(d3D d z * (z * (1 - z))) := by
          linear_combination (-(d2D d z)) * hAid + (z * (1 - z) * d3D d z) * hBid
            + (z ^ 2 * (1 - z) ^ 2) * hcross
        have hexp : z ^ (d - 2) = z * z ^ (d - 3) := by
          have hd3 : d - 2 = (d - 3) + 1 := by omega
          rw [hd3, pow_succ]; ring
        have hPpos : (0:ℝ) < z ^ (d - 3) := pow_pos hz0 _
        have hdpos : (0:ℝ) < (d:ℝ) := by linarith
        have hd1pos : (0:ℝ) < (d:ℝ) - 1 := by linarith
        have hfacz : ((d:ℝ) * ((d:ℝ) - 1) * z ^ (d - 3) * z) * (((d:ℝ) - 1) - (d:ℝ) * z)
            = 0 := by
          have h := hstep
          unfold d2D d3D at h
          rw [hexp] at h
          linear_combination h
        have hnz : ((d:ℝ) * ((d:ℝ) - 1) * z ^ (d - 3) * z) ≠ 0 :=
          ne_of_gt (mul_pos (mul_pos (mul_pos hdpos hd1pos) hPpos) hz0)
        have hfin : ((d:ℝ) - 1) - (d:ℝ) * z = 0 := by
          rcases mul_eq_zero.mp hfacz with h' | h'
          · exact absurd h' hnz
          · exact h'
        refine hstar ?_
        unfold rStar
        rw [eq_div_iff (ne_of_gt hdpos)]
        linear_combination -hfin

end UpperTailOptimizers
