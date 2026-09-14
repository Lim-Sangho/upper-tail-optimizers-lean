import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Inputs
import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.PsiNondeg

/-!
# `thm:krrs-cross-density` with the removable singularity filled in

`paper/sections/preliminaries.tex` defines

  `ψ_d(ε,z) = 2[S₀(z) - S₀(ε) - S₀'(ε)(z-ε)] / (z^d - ε^d - dε^{d-1}(z-ε))`,

"where the removable singularity at `z = ε` is filled in continuously", and
`thm:krrs-cross-density` states that `z ↦ ψ_d(ε,z)` has a unique critical point `ζ_d(ε)` in
`(0,1)`, at which it attains its maximum on `(0,1)`; that `ζ_d : (0,1) → (0,1)` is strictly
decreasing and an involution; and that its unique fixed point is `(d-1)/d`.

`psiD` (`Preliminaries/KRRSAnalyticExtension/Reduced.lean`) is the quotient itself, which Lean evaluates as `0/0 = 0` on the
diagonal.  `psiFill` fills the diagonal with the limit `R_d(ε) = 𝒩''_ε(ε)/𝒟''_ε(ε)`, and
`krrs_cross_density` states the theorem for it.

## The diagonal

With `c := R_d(ε)` put `M(z) = 𝒩_ε(z) - c·𝒟_ε(z)` and `G(z) = (z-ε)·𝒟_ε(z)`.  Off the diagonal
the difference quotient of `psiFill` at `ε` is `M(z)/G(z)`.  Both `M` and `G` vanish at `ε`
together with their first two derivatives, with `M'''(ε) = 𝒩'''(ε) - c·𝒟'''(ε)` and
`G'''(ε) = 3𝒟''(ε) > 0`, while `G'` and `G''` are nonzero at every `z > 0` off the diagonal
(strict convexity of `z ↦ z^d`).  Three applications of L'Hôpital's rule therefore give

  `∂_zψ_d(ε,ε) = (𝒩'''(ε)𝒟''(ε) - 𝒩''(ε)𝒟'''(ε)) / (3𝒟''(ε)²)`
  (`hasDerivAt_psiFill_self`),

so the filled-in function is differentiable (in particular continuous, which shows that `R_d(ε)`
*is* the continuous filling), and the diagonal is critical exactly at `ε = (d-1)/d`
(`diagonalTest_eq_zero_iff`), where `ζ_d` is the identity.

## Contents

* `psiFill_of_ne`, `psiFill_self`, `hasDerivAt_psiFill_of_ne` — off the diagonal;
* `hasDerivAt_psiFill_self`, `differentiableAt_psiFill` — the diagonal derivative;
* `deriv_psiFill_eq_zero_iff` — `ζ_d(ε)` is the only critical point;
* `psiFill_le_zetaFun` — `ζ_d(ε)` is the maximizer, the diagonal value included;
* `krrs_cross_density` — `thm:krrs-cross-density`.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

/-- **`ψ_d(ε,·)` with the removable singularity at `z = ε` filled in**: the quotient `psiD` off the
diagonal, and its limit `R_d(ε) = 𝒩''_ε(ε)/𝒟''_ε(ε)` on it. -/
noncomputable def psiFill (d : ℕ) (ε z : ℝ) : ℝ :=
  if z = ε then Rfun d ε else psiD d ε z

/-! ### Off the diagonal -/

/-- Off the diagonal `psiFill` is the quotient `psiD`. -/
theorem psiFill_of_ne (d : ℕ) {ε z : ℝ} (h : z ≠ ε) : psiFill d ε z = psiD d ε z := if_neg h

/-- On the diagonal `psiFill` is `R_d(ε)`. -/
theorem psiFill_self (d : ℕ) (ε : ℝ) : psiFill d ε ε = Rfun d ε := if_pos rfl

/-- Off the diagonal `psiFill` agrees with `psiD` near `z`, so `∂_zψ_d = W/𝒟²` there. -/
theorem hasDerivAt_psiFill_of_ne {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hz0 : 0 < z)
    (hz1 : z < 1) (hne : z ≠ ε) :
    HasDerivAt (psiFill d ε) (Wr d ε z / Dfun d ε z ^ 2) z := by
  have heq : psiFill d ε =ᶠ[𝓝 z] fun w => psiD d ε w :=
    (eventually_ne_nhds hne).mono fun w hw => psiFill_of_ne d hw
  exact (hasDerivAt_psiD hd hε0 hz0 hz1 hne).congr_of_eventuallyEq heq

/-! ### The diagonal -/

/-- One application of L'Hôpital's rule at a common zero `a` of two functions that are
differentiable near `a`, the derivative of the denominator being nonzero off `a`. -/
private theorem lhopital_step {f f' g g' : ℝ → ℝ} {a l : ℝ}
    (hf : ∀ᶠ x in 𝓝 a, HasDerivAt f (f' x) x) (hg : ∀ᶠ x in 𝓝 a, HasDerivAt g (g' x) x)
    (hfa : f a = 0) (hga : g a = 0) (hg' : ∀ᶠ x in 𝓝[≠] a, g' x ≠ 0)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[≠] a) (𝓝 l)) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 l) := by
  have hfc : Tendsto f (𝓝[≠] a) (𝓝 0) := by
    have h := hf.self_of_nhds.continuousAt.tendsto
    rw [hfa] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  have hgc : Tendsto g (𝓝[≠] a) (𝓝 0) := by
    have h := hg.self_of_nhds.continuousAt.tendsto
    rw [hga] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  exact HasDerivAt.lhopital_zero_nhdsNE (eventually_nhdsWithin_of_eventually_nhds hf)
    (eventually_nhdsWithin_of_eventually_nhds hg) hg' hfc hgc hdiv

/-- `(z-ε)·𝒟'_ε(z) > 0` for `z > 0` off the diagonal: `𝒟'_ε` changes sign at `ε`. -/
private theorem sub_mul_dD_pos {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε0 : 0 < ε) (hz0 : 0 < z)
    (hne : z ≠ ε) : 0 < (z - ε) * dD d ε z := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := dD_pos hd hz0 hlt
    rw [dD_swap] at h
    exact mul_pos_of_neg_of_neg (sub_neg.2 hlt) (neg_pos.1 h)
  · exact mul_pos (sub_pos.2 hgt) (dD_pos hd hε0 hgt)

/-- **The derivative of the filled-in `ψ_d(ε,·)` on the diagonal**:

  `∂_zψ_d(ε,ε) = (𝒩'''(ε)𝒟''(ε) - 𝒩''(ε)𝒟'''(ε)) / (3𝒟''(ε)²)`.

The difference quotient at `ε` is `M/G` with `M = 𝒩_ε - R_d(ε)𝒟_ε` and `G = (z-ε)𝒟_ε`, and
three applications of L'Hôpital's rule reduce it to `M'''/G'''`, which is continuous at `ε`. -/
theorem hasDerivAt_psiFill_self {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    HasDerivAt (psiFill d ε)
      ((d3N ε * d2D d ε - d2N ε * d3D d ε) / (3 * d2D d ε ^ 2)) ε := by
  set c := Rfun d ε with hc
  have hD2 : 0 < d2D d ε := d2D_pos hd hε0
  have hnear : ∀ᶠ x in 𝓝 ε, x ∈ Ioo (0:ℝ) 1 := Ioo_mem_nhds hε0 hε1
  have hpunct : ∀ᶠ x in 𝓝[≠] ε, 0 < x ∧ x ≠ ε :=
    (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds hε0)).and
      (eventually_mem_nhdsWithin.mono fun x hx => hx)
  -- the numerator `M` and its derivatives
  have hM0 : ∀ᶠ x in 𝓝 ε, HasDerivAt (fun w => Nfun ε w - c * Dfun d ε w)
      (dN ε x - c * dD d ε x) x :=
    hnear.mono fun x hx =>
      (hasDerivAt_Nfun ε hx.1.ne' hx.2.ne).sub ((hasDerivAt_Dfun d ε x).const_mul c)
  have hM1 : ∀ᶠ x in 𝓝 ε, HasDerivAt (fun w => dN ε w - c * dD d ε w)
      (d2N x - c * d2D d x) x :=
    hnear.mono fun x hx =>
      (hasDerivAt_dN ε hx.1.ne' hx.2.ne).sub ((hasDerivAt_dD hd ε x).const_mul c)
  have hM2 : ∀ᶠ x in 𝓝 ε, HasDerivAt (fun w => d2N w - c * d2D d w)
      (d3N x - c * d3D d x) x :=
    hnear.mono fun x hx =>
      (hasDerivAt_d2N hx.1.ne' hx.2.ne).sub ((hasDerivAt_d2D hd x).const_mul c)
  -- the denominator `G` and its derivatives
  have hG0 : ∀ᶠ x in 𝓝 ε, HasDerivAt (fun w => (w - ε) * Dfun d ε w)
      (Dfun d ε x + (x - ε) * dD d ε x) x :=
    Eventually.of_forall fun x =>
      (((hasDerivAt_id' x).sub_const ε).mul (hasDerivAt_Dfun d ε x)).congr_deriv (by ring)
  have hG1 : ∀ᶠ x in 𝓝 ε, HasDerivAt (fun w => Dfun d ε w + (w - ε) * dD d ε w)
      (2 * dD d ε x + (x - ε) * d2D d x) x :=
    Eventually.of_forall fun x =>
      ((hasDerivAt_Dfun d ε x).add
        (((hasDerivAt_id' x).sub_const ε).mul (hasDerivAt_dD hd ε x))).congr_deriv (by ring)
  have hG2 : ∀ᶠ x in 𝓝 ε, HasDerivAt (fun w => 2 * dD d ε w + (w - ε) * d2D d w)
      (3 * d2D d x + (x - ε) * d3D d x) x :=
    Eventually.of_forall fun x =>
      (((hasDerivAt_dD hd ε x).const_mul 2).add
        (((hasDerivAt_id' x).sub_const ε).mul (hasDerivAt_d2D hd x))).congr_deriv (by ring)
  -- the derivatives of `G` do not vanish off the diagonal
  have hG1ne : ∀ᶠ x in 𝓝[≠] ε, Dfun d ε x + (x - ε) * dD d ε x ≠ 0 :=
    hpunct.mono fun x hx =>
      (add_pos (Dfun_pos hd hε0 hx.1.le hx.2) (sub_mul_dD_pos hd hε0 hx.1 hx.2)).ne'
  have hG2ne : ∀ᶠ x in 𝓝[≠] ε, 2 * dD d ε x + (x - ε) * d2D d x ≠ 0 :=
    hpunct.mono fun x hx h => by
      have h1 := sub_mul_dD_pos hd hε0 hx.1 hx.2
      have h2 : 0 < (x - ε) ^ 2 * d2D d x :=
        mul_pos (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (sub_ne_zero.2 hx.2)).symm)
          (d2D_pos hd hx.1)
      have h3 : (x - ε) * (2 * dD d ε x + (x - ε) * d2D d x)
          = 2 * ((x - ε) * dD d ε x) + (x - ε) ^ 2 * d2D d x := by ring
      rw [h, mul_zero] at h3
      linarith
  -- continuity of `M'''/G'''` at the diagonal
  have hd3N : ContinuousAt d3N ε := by
    show ContinuousAt (fun z : ℝ => (1 - 2 * z) / (z ^ 2 * (1 - z) ^ 2)) ε
    exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (mul_ne_zero (pow_ne_zero _ hε0.ne') (pow_ne_zero _ (sub_pos.2 hε1).ne'))
  have hd2D : Continuous (d2D d) := by
    show Continuous fun z : ℝ => (d : ℝ) * ((d : ℝ) - 1) * z ^ (d - 2)
    fun_prop
  have hd3D : Continuous (d3D d) := by
    show Continuous fun z : ℝ => (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * z ^ (d - 3)
    fun_prop
  have hG3cont : ContinuousAt (fun x => 3 * d2D d x + (x - ε) * d3D d x) ε :=
    ((hd2D.continuousAt.const_mul 3).add
      ((continuousAt_id.sub continuousAt_const).mul hd3D.continuousAt))
  have hG3ε : 3 * d2D d ε + (ε - ε) * d3D d ε ≠ 0 := by
    rw [sub_self, zero_mul, add_zero]
    exact (mul_pos three_pos hD2).ne'
  have hG3ne : ∀ᶠ x in 𝓝[≠] ε, 3 * d2D d x + (x - ε) * d3D d x ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds (hG3cont.eventually_ne hG3ε)
  have h3 : Tendsto (fun x => (d3N x - c * d3D d x) / (3 * d2D d x + (x - ε) * d3D d x))
      (𝓝[≠] ε) (𝓝 ((d3N ε * d2D d ε - d2N ε * d3D d ε) / (3 * d2D d ε ^ 2))) := by
    have hcont : ContinuousAt
        (fun x => (d3N x - c * d3D d x) / (3 * d2D d x + (x - ε) * d3D d x)) ε :=
      (hd3N.sub (hd3D.continuousAt.const_mul c)).div hG3cont hG3ε
    have h := tendsto_nhdsWithin_of_tendsto_nhds (s := {ε}ᶜ) hcont.tendsto
    convert h using 2
    rw [hc, Rfun]
    field_simp
    ring
  -- three applications of L'Hôpital's rule
  have hM2ε : d2N ε - c * d2D d ε = 0 := by
    rw [hc, Rfun, div_mul_cancel₀ _ hD2.ne', sub_self]
  have hM1ε : dN ε ε - c * dD d ε ε = 0 := by unfold dN dD; ring
  have hM0ε : Nfun ε ε - c * Dfun d ε ε = 0 := by unfold Nfun Dfun; ring
  have hG2ε : 2 * dD d ε ε + (ε - ε) * d2D d ε = 0 := by unfold dD; ring
  have hG1ε : Dfun d ε ε + (ε - ε) * dD d ε ε = 0 := by unfold Dfun; ring
  have hG0ε : (ε - ε) * Dfun d ε ε = 0 := by ring
  have h2 := lhopital_step hM2 hG2 hM2ε hG2ε hG3ne h3
  have h1 := lhopital_step hM1 hG1 hM1ε hG1ε hG2ne h2
  have h0 := lhopital_step hM0 hG0 hM0ε hG0ε hG1ne h1
  -- the difference quotient of `psiFill` is `M/G`
  rw [hasDerivAt_iff_tendsto_slope]
  refine h0.congr' ?_
  filter_upwards [hpunct] with x hx
  rw [slope_def_field, psiFill_of_ne d hx.2, psiFill_self]
  have hD : Dfun d ε x ≠ 0 := (Dfun_pos hd hε0 hx.1.le hx.2).ne'
  have hxe : x - ε ≠ 0 := sub_ne_zero.2 hx.2
  unfold psiD
  field_simp
  rw [hc]
  ring

/-- The filled-in `ψ_d(ε,·)` is differentiable throughout `(0,1)`. -/
theorem differentiableAt_psiFill {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hz : z ∈ Ioo (0:ℝ) 1) : DifferentiableAt ℝ (psiFill d ε) z := by
  by_cases hne : z = ε
  · rw [hne]
    exact (hasDerivAt_psiFill_self hd hε.1 hε.2).differentiableAt
  · exact (hasDerivAt_psiFill_of_ne hd hε.1 hz.1 hz.2 hne).differentiableAt

/-! ### The critical point and the maximum -/

/-- `ζ_d` fixes exactly the exceptional density. -/
theorem zetaFun_eq_self_iff {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1) :
    zetaFun d ε = ε ↔ ε = rStar d := by
  constructor
  · intro h
    by_contra hne
    exact zetaFun_ne_self hd hε hne h
  · intro h
    rw [h]
    exact zetaFun_rStar hd

/-- **`ζ_d(ε)` is the unique critical point of the filled-in `ψ_d(ε,·)` in `(0,1)`.**  Off the
diagonal this is `W(ε,z) = 0 ↔ z = ζ_d(ε)`; on it, the diagonal derivative vanishes exactly at
`ε = (d-1)/d`, which is exactly when `ζ_d(ε) = ε`. -/
theorem deriv_psiFill_eq_zero_iff {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hz : z ∈ Ioo (0:ℝ) 1) : deriv (psiFill d ε) z = 0 ↔ z = zetaFun d ε := by
  by_cases hne : z = ε
  · rw [hne, (hasDerivAt_psiFill_self hd hε.1 hε.2).deriv, div_eq_zero_iff, sub_eq_zero,
      eq_comm (a := ε), zetaFun_eq_self_iff hd hε,
      or_iff_left (mul_ne_zero three_ne_zero (pow_ne_zero 2 (d2D_pos hd hε.1).ne'))]
    exact eq_comm.trans (diagonalTest_eq_zero_iff hd hε.1 hε.2)
  · rw [(hasDerivAt_psiFill_of_ne hd hε.1 hz.1 hz.2 hne).deriv, div_eq_zero_iff,
      or_iff_left (pow_ne_zero 2 (Dfun_pos hd hε.1 hz.1.le hne).ne')]
    refine ⟨zetaFun_eq_of_crit hd hε hz hne, fun h => ?_⟩
    rw [h]
    exact zetaFun_Wr_eq_zero hd hε

/-- **`ζ_d(ε)` maximises the filled-in `ψ_d(ε,·)` on `(0,1)`.**  Off the diagonal this is
`zetaFun_isMax`.  The diagonal value `R_d(ε)` is beaten by `ψ_d(ε,r_*)` when `ε ≠ r_*`
(`lt_psiD_of_lt_Rfun`, since `R_d` increases from `ε` towards its maximum at `r_*`); and at
`ε = r_*`, where `ζ_d(ε) = ε`, every off-diagonal value lies below `R_d(r_*)`
(`psiD_lt_of_Rfun_lt`). -/
theorem psiFill_le_zetaFun {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε : ε ∈ Ioo (0:ℝ) 1)
    (hz : z ∈ Ioo (0:ℝ) 1) : psiFill d ε z ≤ psiFill d ε (zetaFun d ε) := by
  have hr0 : 0 < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  by_cases hεr : ε = rStar d
  · rw [(zetaFun_eq_self_iff hd hε).2 hεr, psiFill_self]
    by_cases hzε : z = ε
    · rw [hzε, psiFill_self]
    · rw [psiFill_of_ne d hzε]
      refine (psiD_lt_of_Rfun_lt hd hε.1 hε.2 hz.1 hz.2 hzε (fun s hs => ?_)).le
      rcases lt_or_gt_of_ne hzε with hlt | hgt
      · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hs
        rw [hεr] at hs ⊢
        exact Rfun_strictMonoOn hd ⟨lt_trans hz.1 hs.1, hs.2.le⟩ ⟨hr0, le_rfl⟩ hs.2
      · rw [min_eq_left hgt.le, max_eq_right hgt.le] at hs
        rw [hεr] at hs ⊢
        exact Rfun_strictAntiOn hd ⟨le_rfl, hr1⟩ ⟨hs.1.le, lt_trans hs.2 hz.2⟩ hs.1
  · rw [psiFill_of_ne d (zetaFun_ne_self hd hε hεr)]
    by_cases hzε : z = ε
    · rw [hzε, psiFill_self]
      have hrε : rStar d ≠ ε := Ne.symm hεr
      have h1 : Rfun d ε < psiD d ε (rStar d) := by
        refine lt_psiD_of_lt_Rfun hd hε.1 hε.2 hr0 hr1 hrε (fun s hs => ?_)
        rcases lt_or_gt_of_ne hεr with hlt | hgt
        · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hs
          exact Rfun_strictMonoOn hd ⟨hε.1, hlt.le⟩ ⟨lt_trans hε.1 hs.1, hs.2.le⟩ hs.1
        · rw [min_eq_right hgt.le, max_eq_left hgt.le] at hs
          exact Rfun_strictAntiOn hd ⟨hs.1.le, lt_trans hs.2 hε.2⟩ ⟨hgt.le, hε.2⟩ hs.2
      exact (h1.trans_le (zetaFun_isMax hd hε (rStar d) ⟨hr0, hr1⟩ hrε)).le
    · rw [psiFill_of_ne d hzε]
      exact zetaFun_isMax hd hε z hz hzε

/-- **`thm:krrs-cross-density`** (KRR–S cross density for regular graphs).  For `d ≥ 2` and
`ε ∈ (0,1)`, the filled-in `z ↦ ψ_d(ε,z)` is differentiable on `(0,1)`, its only critical point
in `(0,1)` is `ζ_d(ε)`, and it attains its maximum on `(0,1)` there.  The map `ζ_d` sends
`(0,1)` to `(0,1)`, is strictly decreasing and an involution, and its unique fixed point is
`(d-1)/d`. -/
theorem krrs_cross_density {d : ℕ} (hd : 2 ≤ d) :
    (∀ ε ∈ Set.Ioo (0:ℝ) 1,
      (∀ z ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ (psiFill d ε) z) ∧
      zetaFun d ε ∈ Set.Ioo (0:ℝ) 1 ∧
      (∀ z ∈ Set.Ioo (0:ℝ) 1, deriv (psiFill d ε) z = 0 ↔ z = zetaFun d ε) ∧
      (∀ z ∈ Set.Ioo (0:ℝ) 1, psiFill d ε z ≤ psiFill d ε (zetaFun d ε))) ∧
    StrictAntiOn (zetaFun d) (Set.Ioo 0 1) ∧
    (∀ ε ∈ Set.Ioo (0:ℝ) 1, zetaFun d (zetaFun d ε) = ε) ∧
    (∀ ε ∈ Set.Ioo (0:ℝ) 1, zetaFun d ε = ε ↔ ε = rStar d) :=
  ⟨fun _ hε => ⟨fun _ hz => differentiableAt_psiFill hd hε hz, zetaFun_mem hd hε,
      fun _ hz => deriv_psiFill_eq_zero_iff hd hε hz, fun _ hz => psiFill_le_zetaFun hd hε hz⟩,
    zetaFun_strictAntiOn hd, fun _ hε => zetaFun_involutive hd hε,
    fun _ hε => zetaFun_eq_self_iff hd hε⟩

end UpperTailOptimizers
