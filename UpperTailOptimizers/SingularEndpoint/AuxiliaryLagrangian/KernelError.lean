import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.KernelTheta
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.PowFirstOrder

/-!
# The corner error of `lem:central-kernel-bound` (Section 5, `paper/sections/singular_auxiliary_lagrangian.tex`)

The corner quotient `Θ_h` of `lem:central-kernel-bound` converges to the
constant `d³/4` of `SingularEndpoint/AuxiliaryLagrangian/KernelTheta.lean`, uniformly on the central square and uniformly
in small `h`.  The target is stated **unwound**, as

  `∀ ε > 0, ∃ ρ > 0, ∃ h_ρ > 0, ∀ 0 < h < h_ρ, ∀ x y ∈ 𝓝_ρ,
     |Θ_h(x,y) - d³/4| ≤ ε`

(`KKTFamily.exists_kernelTheta_error`), which is what the quantitative half of
`lem:auxiliary-lagrangian-bound` consumes.  The paper instead obtains
`sup_{0<h<h_ρ}‖Θ_h - d³/4‖_{L^∞(𝒩_ρ²)} ≤ a/4` from "the joint continuity of `Θ_h(x,y)` at
`(h,x,y) = (0,u_*,u_*)`"; the unwound form, for every accuracy `ε`, avoids having to produce
the supremum before the boundedness that this file proves.

## The route: two mean-value steps, and a parameter derivative for `powDD`

`KKTFamily.kernelTheta` is `mfac(x)·mfac(y)` times the divided difference **in the first
variable** of the divided difference in the second,

  `Θ_h(x,y)/(mfac·mfac) = powDD_z (z ↦ powDD_w K_h(z,·) at y) at x`.

`SingularEndpoint/AuxiliaryLagrangian/PowInterp.lean` already sandwiches a single `powDD` between `m/2` and `M/2`
(`powDD_mem_of_powDeriv2_mem`), at the nodes as well, so the outer step only needs a
**derivative chain in the frozen variable** for `z ↦ powDD d (K_h(z,·)) s_h t_h y`.  That is
the one missing ingredient, and it is supplied here without any analyticity input:

* `powDD_of_ne`, `powDD_left`, `powDD_right` write `powDD d φ s t y` as an **explicit** fixed
  linear combination of `φ(s)`, `φ(t)`, `φ(y)` and — when `y` is one of the two nodes — of
  `powDeriv d φ₁` at that node.  There are three cases, and which one applies depends only on
  the *evaluation point* `y`, never on the parameter; the coefficients are parameter-free.
* `hasDerivAt_powDD_param` differentiates that combination in the parameter.  The only
  hypothesis beyond the obvious parameter derivatives is the equality of the two mixed
  derivatives at the nodes, and for the law kernel `K_h(z,w) = J_{p_h}(zw)` both are
  computed in closed form (`hasDerivAt_kSlice0w_fst` versus `hasDerivAt_kSlice1_snd`).

The kernel slices `kSlice0, kSlice1, kSlice2` are `K_h(z,·)` and its first two derivatives in
the frozen variable, `kSlice·w`, `kSlice·ww` their derivatives in the free variable; the
twelve `hasDerivAt_kSlice…` lemmas are the whole derivative table of `J_{p_h}(zw)` up to total
order four.  `thetaV0`, `thetaV1`, `thetaV2` are the corresponding `powDeriv2`, i.e. the
second derivative in the chart `v = w^d`, which is exactly what the sandwich bounds.

## The corner constant

`powDopOf_powDopOf_kernel` (`SingularEndpoint/AuxiliaryLagrangian/KernelTheta.lean`) already evaluates the iterated
operator `𝒟_{d,x}𝒟_{d,y}K_0` at `(u_*,u_*)` as `d³/4`.  `thetaV_theta_value` transports it
into the chart: `powDopOf_kernel_slice_eq_thetaV0` identifies the inner operator with
`(d²u_*^{2d-2}/2)·thetaV0`, and `hasDerivAt_thetaV0_fst`, `hasDerivAt_thetaV1_fst`
differentiate that identification twice, so that the outer operator is
`(d²u_*^{2d-2}/2)²·powDeriv2` of the pair `(thetaV1, thetaV2)`.  Two applications of
`powDop_eq_powDeriv2` — one per chart — are what the two factors `d²u_*^{2d-2}/2` are.

## `h`-uniformity

No compactness argument in `h` is used.  `Jp''`, `Jp3`, `Jp4` do not mention `p` at all, and
`J_p'` moves with `p` only by the **constant** `Λ_p = ℓ(p) - ℓ(p_*)` (`Jp'_eq_Jp'_pStar_add`,
`SingularEndpoint/AuxiliaryLagrangian/PowFirstOrder.lean`); `thetaV1_sub_pStar` records that `thetaV1` inherits exactly
that displacement, divided by `d²w^{2d-1}`, and `thetaV2` does not move at all.  The whole
`h`-dependence of the estimate is therefore the single scalar `Λ_h → 0`.

## Contents

* `powDD_of_ne`, `powDD_left`, `powDD_right` — the three explicit forms of `powDD`;
* `hasDerivAt_powDD_param` — the parameter derivative of `powDD`;
* `kSlice0`, `kSlice0w`, `kSlice0ww`, `kSlice1`, `kSlice1w`, `kSlice1ww`, `kSlice2`,
  `kSlice2w`, `kSlice2ww` and their twelve `HasDerivAt` lemmas;
* `thetaV0`, `thetaV1`, `thetaV2`, `thetaV1_eq`, `thetaV2_eq`, `thetaV1_sub_pStar`;
* `hasDerivAt_thetaV0_fst`, `hasDerivAt_thetaV1_fst`,
  `powDopOf_kernel_slice_eq_thetaV0`, `thetaV_theta_value` — the constant `d³/4` in the
  chart;
* `KKTFamily.hasDerivAt_thetaSlice`, `.hasDerivAt_thetaSlice1` — the derivative chain
  in the frozen variable;
* `KKTFamily.thetaSlice1_mem`, `.thetaSlice2_mem` — the two inner sandwiches;
* `KKTFamily.exists_kernelTheta_error` — **the corner error of `lem:central-kernel-bound`**;
* `abs_powDeriv2_le`, `KKTFamily.hasDerivAt_kernelCoefA_fst`, `.hasDerivAt_kernelCoefB_fst`,
  `.exists_u0_window`, `.exists_ud_window`, `.exists_kernelTheta_bound` — the coefficient-bound
  clause `max{|p_{ij,h}|, |u_{i,h}(x)|, |v_{i,h}(y)|} ≤ C_d` of the proof of
  `lem:central-kernel-bound` for the one-variable functions `u_{0,h}`, `u_{d,h}`
  (`= v_{0,h}, v_{d,h}` by symmetry of the kernel), together with a bound on `Θ_h`; these were
  left open by `SingularEndpoint/AuxiliaryLagrangian/PowFirstOrder.lean`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

/-! ## `dslope` as an honest quotient -/

/-- Mathlib's `dslope f a` is the ordinary difference quotient away from the base point.  A
sign-normalised restatement of `dslope_of_ne`, derived from the multiplicative identity
`sub_mul_dslope` so that no convention about `slope` enters. -/
private theorem dslope_eq_div {f : ℝ → ℝ} {a z : ℝ} (h : z ≠ a) :
    dslope f a z = (f z - f a) / (z - a) := by
  rw [eq_div_iff (sub_ne_zero.mpr h)]
  linear_combination sub_mul_dslope f a z

/-- Distinct nonnegative reals have distinct `d`-th powers, `d ≠ 0`.  The bookkeeping behind
each of the three cases below: in the chart `w = x^d` the nodes `s^d, t^d` and the evaluation
point `x^d` are distinct exactly when `s, t, x` are. -/
private theorem pow_ne_pow_of_ne {d : ℕ} (hd : d ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) : a ^ d ≠ b ^ d := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact ne_of_lt (pow_lt_pow_left₀ h ha hd)
  · exact ne_of_gt (pow_lt_pow_left₀ h hb hd)

/-! ## The three explicit forms of `powDD`

`powDD d φ s t x = dd2 (powChart d φ) (s^d) (t^d) (x^d)` is *total*, so it has a value at the
nodes as well; the three lemmas below are that value, in each case a fixed linear combination
of `φ(s)`, `φ(t)`, `φ(x)` and `powDeriv d φ₁` at a node, with coefficients depending only on
`d, s, t, x`.  Which case applies is decided by the evaluation point `x` alone. -/

/-- **Off the nodes**: the ordinary second divided difference in the chart `w = x^d`. -/
theorem powDD_of_ne {d : ℕ} (hd : d ≠ 0) (phi : ℝ → ℝ) {s t x : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hst : s < t) (hxs : x ≠ s) (hxt : x ≠ t) :
    powDD d phi s t x
      = ((phi x - phi s) / (x ^ d - s ^ d) - (phi t - phi s) / (t ^ d - s ^ d))
          / (x ^ d - t ^ d) := by
  have hxs' : x ^ d ≠ s ^ d := pow_ne_pow_of_ne hd hx hs hxs
  have hxt' : x ^ d ≠ t ^ d := pow_ne_pow_of_ne hd hx ht hxt
  have hts' : t ^ d ≠ s ^ d := pow_ne_pow_of_ne hd ht hs (ne_of_gt hst)
  simp only [powDD, dd2]
  rw [dslope_eq_div hxt', dslope_eq_div hxs', dslope_eq_div hts', powChart_pow hd phi hx,
    powChart_pow hd phi hs, powChart_pow hd phi ht]

/-- **At the lower node**: `powDD` reads the derivative of `φ` there, through the chart
derivative `powDeriv d φ₁ s = φ₁(s)/(d s^{d-1})`. -/
theorem powDD_left {d : ℕ} (hd : d ≠ 0) {phi phi1 : ℝ → ℝ} {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    (hst : s < t) (hder : HasDerivAt phi (phi1 s) s) :
    powDD d phi s t s
      = ((phi t - phi s) - powDeriv d phi1 s * (t ^ d - s ^ d)) / (t ^ d - s ^ d) ^ 2 := by
  have hts' : t ^ d ≠ s ^ d := pow_ne_pow_of_ne hd ht hs.le (ne_of_gt hst)
  have hD : t ^ d - s ^ d ≠ 0 := sub_ne_zero.mpr hts'
  have hD' : s ^ d - t ^ d ≠ 0 := sub_ne_zero.mpr (Ne.symm hts')
  have hchart : HasDerivAt (powChart d phi) (powDeriv d phi1 s) (s ^ d) :=
    hasDerivAt_powChart hd hs hder
  have e0 : dslope (powChart d phi) (s ^ d) (s ^ d) = powDeriv d phi1 s := by
    rw [dslope_same]
    exact hchart.deriv
  simp only [powDD, dd2]
  rw [dslope_eq_div (Ne.symm hts'), e0, dslope_eq_div hts', powChart_pow hd phi ht,
    powChart_pow hd phi hs.le]
  field_simp
  ring

/-- **At the upper node**: there `dd2` is an honest derivative of the difference quotient, and
the quotient rule gives the mirror image of `powDD_left`. -/
theorem powDD_right {d : ℕ} (hd : d ≠ 0) {phi phi1 : ℝ → ℝ} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t)
    (hst : s < t) (hder : HasDerivAt phi (phi1 t) t) :
    powDD d phi s t t
      = (powDeriv d phi1 t * (t ^ d - s ^ d) - (phi t - phi s)) / (t ^ d - s ^ d) ^ 2 := by
  have hts' : t ^ d ≠ s ^ d := pow_ne_pow_of_ne hd ht.le hs (ne_of_gt hst)
  have hD : t ^ d - s ^ d ≠ 0 := sub_ne_zero.mpr hts'
  have hchart : HasDerivAt (powChart d phi) (powDeriv d phi1 t) (t ^ d) :=
    hasDerivAt_powChart hd ht hder
  have hq : HasDerivAt (fun w : ℝ => (powChart d phi w - powChart d phi (s ^ d)) / (w - s ^ d))
      ((powDeriv d phi1 t * (t ^ d - s ^ d)
          - (powChart d phi (t ^ d) - powChart d phi (s ^ d)) * 1) / (t ^ d - s ^ d) ^ 2)
      (t ^ d) :=
    (hchart.sub_const _).div ((hasDerivAt_id _).sub_const _) hD
  have heq : dslope (powChart d phi) (s ^ d)
      =ᶠ[𝓝 (t ^ d)] fun w : ℝ => (powChart d phi w - powChart d phi (s ^ d)) / (w - s ^ d) := by
    filter_upwards [isOpen_ne.mem_nhds hts'] with w hw
    exact dslope_eq_div hw
  have hder2 := hq.congr_of_eventuallyEq heq
  have h0 : powDD d phi s t t = deriv (dslope (powChart d phi) (s ^ d)) (t ^ d) :=
    dslope_same _ _
  rw [h0, hder2.deriv, powChart_pow hd phi ht.le, powChart_pow hd phi hs]
  ring

/-! ## The parameter derivative of `powDD` -/

/-- **`powDD` may be differentiated in a parameter.**  For a family `f ζ` of functions with
parameter derivative `g z`, whose derivatives in the free variable at the two nodes are
`fv ζ` with parameter derivative `gv z`,

  `∂_ζ (powDD d (f ζ) s t y) = powDD d (g z) s t y`.

The proof is the three-case analysis of `powDD_of_ne`, `powDD_left`, `powDD_right`: in each
case both sides are the *same* fixed linear combination, of `f`-data on the left and of
`g`-data on the right, so the statement is an application of the sum, product and quotient
rules.  The case is decided by the evaluation point `y`, which does not move with `ζ`; the
node hypotheses `hws`, `hwt` are needed only in the two degenerate cases and are asked for
locally in `ζ`, which is all a derivative sees. -/
theorem hasDerivAt_powDD_param {d : ℕ} (hd : d ≠ 0) {f g fv gv : ℝ → ℝ → ℝ} {s t y z : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hy : 0 ≤ y) (hst : s < t)
    (hfs : HasDerivAt (fun ζ => f ζ s) (g z s) z)
    (hft : HasDerivAt (fun ζ => f ζ t) (g z t) z)
    (hfy : HasDerivAt (fun ζ => f ζ y) (g z y) z)
    (hfvs : HasDerivAt (fun ζ => fv ζ s) (gv z s) z)
    (hfvt : HasDerivAt (fun ζ => fv ζ t) (gv z t) z)
    (hws : ∀ᶠ ζ in 𝓝 z, HasDerivAt (f ζ) (fv ζ s) s)
    (hwt : ∀ᶠ ζ in 𝓝 z, HasDerivAt (f ζ) (fv ζ t) t)
    (hgs : HasDerivAt (g z) (gv z s) s) (hgt : HasDerivAt (g z) (gv z t) t) :
    HasDerivAt (fun ζ => powDD d (f ζ) s t y) (powDD d (g z) s t y) z := by
  by_cases hys : y = s
  · rw [hys]
    have hfun : (fun ζ => powDD d (f ζ) s t s)
        =ᶠ[𝓝 z] fun ζ => ((f ζ t - f ζ s) - powDeriv d (fv ζ) s * (t ^ d - s ^ d))
            / (t ^ d - s ^ d) ^ 2 := by
      filter_upwards [hws] with ζ hζ
      exact powDD_left hd hs ht.le hst hζ
    rw [powDD_left hd hs ht.le hst hgs]
    refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
    have hpd : HasDerivAt (fun ζ => powDeriv d (fv ζ) s) (powDeriv d (gv z) s) z := by
      simpa only [powDeriv] using hfvs.div_const ((d : ℝ) * s ^ (d - 1))
    exact ((hft.sub hfs).sub (hpd.mul_const (t ^ d - s ^ d))).div_const ((t ^ d - s ^ d) ^ 2)
  · by_cases hyt : y = t
    · rw [hyt]
      have hfun : (fun ζ => powDD d (f ζ) s t t)
          =ᶠ[𝓝 z] fun ζ => (powDeriv d (fv ζ) t * (t ^ d - s ^ d) - (f ζ t - f ζ s))
              / (t ^ d - s ^ d) ^ 2 := by
        filter_upwards [hwt] with ζ hζ
        exact powDD_right hd hs.le ht hst hζ
      rw [powDD_right hd hs.le ht hst hgt]
      refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
      have hpd : HasDerivAt (fun ζ => powDeriv d (fv ζ) t) (powDeriv d (gv z) t) z := by
        simpa only [powDeriv] using hfvt.div_const ((d : ℝ) * t ^ (d - 1))
      exact ((hpd.mul_const (t ^ d - s ^ d)).sub (hft.sub hfs)).div_const ((t ^ d - s ^ d) ^ 2)
    · have hfun : (fun ζ => powDD d (f ζ) s t y)
          = fun ζ => ((f ζ y - f ζ s) / (y ^ d - s ^ d)
              - (f ζ t - f ζ s) / (t ^ d - s ^ d)) / (y ^ d - t ^ d) := by
        funext ζ
        exact powDD_of_ne hd (f ζ) hs.le ht.le hy hst hys hyt
      rw [hfun, powDD_of_ne hd (g z) hs.le ht.le hy hst hys hyt]
      exact (((hfy.sub hfs).div_const (y ^ d - s ^ d)).sub
        ((hft.sub hfs).div_const (t ^ d - s ^ d))).div_const (y ^ d - t ^ d)

/-! ## The derivative table of the law kernel `K(z,w) = J_p(zw)`

Nine functions: `kSlice0, kSlice1, kSlice2` are `K(z,·)` and its first two derivatives in the
frozen variable `z`, and the suffixes `w`, `ww` are one and two derivatives in the free
variable `w`.  Only `kSlice0`, `kSlice0w`, `kSlice1`, `kSlice1w` mention `p` — from `J_p''`
onwards the entropy derivatives are `p`-free. -/

/-- The kernel slice `w ↦ J_p(zw)`; this is `KKTFamily.kernel` with the family data
substituted. -/
noncomputable def kSlice0 (p z w : ℝ) : ℝ := Jp p (z * w)

/-- `∂_w K(z,w) = z J_p'(zw)`. -/
noncomputable def kSlice0w (p z w : ℝ) : ℝ := z * Jp' p (z * w)

/-- `∂_w² K(z,w) = z² J_p''(zw)`. -/
noncomputable def kSlice0ww (z w : ℝ) : ℝ := z ^ 2 * Jp'' (z * w)

/-- `∂_z K(z,w) = w J_p'(zw)`. -/
noncomputable def kSlice1 (p z w : ℝ) : ℝ := w * Jp' p (z * w)

/-- `∂_w∂_z K(z,w) = J_p'(zw) + wz J_p''(zw)`. -/
noncomputable def kSlice1w (p z w : ℝ) : ℝ := Jp' p (z * w) + w * z * Jp'' (z * w)

/-- `∂_w²∂_z K(z,w) = 2z J_p''(zw) + wz² J_p'''(zw)`. -/
noncomputable def kSlice1ww (z w : ℝ) : ℝ := 2 * z * Jp'' (z * w) + w * z ^ 2 * Jp3 (z * w)

/-- `∂_z² K(z,w) = w² J_p''(zw)`. -/
noncomputable def kSlice2 (z w : ℝ) : ℝ := w ^ 2 * Jp'' (z * w)

/-- `∂_w∂_z² K(z,w) = 2w J_p''(zw) + w²z J_p'''(zw)`. -/
noncomputable def kSlice2w (z w : ℝ) : ℝ := 2 * w * Jp'' (z * w) + w ^ 2 * z * Jp3 (z * w)

/-- `∂_w²∂_z² K(z,w) = 2J_p''(zw) + 4wz J_p'''(zw) + w²z² J_p''''(zw)`.  This is the quantity
whose value at the corner produces the constant `d³/4`. -/
noncomputable def kSlice2ww (z w : ℝ) : ℝ :=
  2 * Jp'' (z * w) + 4 * w * z * Jp3 (z * w) + w ^ 2 * z ^ 2 * Jp4 (z * w)

section Table

variable {p z w : ℝ}

/-- The chain rule through `v ↦ zv`, the inner map of every free-variable derivative below. -/
private theorem hasDerivAt_comp_mul_left {f : ℝ → ℝ} {c z w : ℝ} (h : HasDerivAt f c (z * w)) :
    HasDerivAt (fun v : ℝ => f (z * v)) (c * z) w := by
  have hinner : HasDerivAt (fun v : ℝ => z * v) z w := by
    simpa using (hasDerivAt_id w).const_mul z
  have hcomp := h.comp w hinner
  have hfun : (f ∘ fun v : ℝ => z * v) = fun v : ℝ => f (z * v) := rfl
  rwa [hfun] at hcomp

/-- The chain rule through `ζ ↦ ζw`, the inner map of every frozen-variable derivative
below. -/
private theorem hasDerivAt_comp_mul_right {f : ℝ → ℝ} {c z w : ℝ} (h : HasDerivAt f c (z * w)) :
    HasDerivAt (fun ζ : ℝ => f (ζ * w)) (c * w) z := by
  have hinner : HasDerivAt (fun ζ : ℝ => ζ * w) w z := by
    simpa using (hasDerivAt_id z).mul_const w
  have hcomp := h.comp z hinner
  have hfun : (f ∘ fun ζ : ℝ => ζ * w) = fun ζ : ℝ => f (ζ * w) := rfl
  rwa [hfun] at hcomp

/-- `∂_w kSlice0 = kSlice0w`. -/
theorem hasDerivAt_kSlice0_snd (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (kSlice0 p z) (kSlice0w p z w) w := by
  have hcomp : HasDerivAt (fun v : ℝ => Jp p (z * v)) (Jp' p (z * w) * z) w :=
    hasDerivAt_comp_mul_left (hasDerivAt_Jp hp0 hp1 h0 h1)
  exact hcomp.congr_deriv (by simp only [kSlice0w]; ring)

/-- `∂_w kSlice0w = kSlice0ww`. -/
theorem hasDerivAt_kSlice0w_snd (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (kSlice0w p z) (kSlice0ww z w) w := by
  have hcomp : HasDerivAt (fun v : ℝ => Jp' p (z * v)) (Jp'' (z * w) * z) w :=
    hasDerivAt_comp_mul_left (hasDerivAt_Jp' hp0 hp1 h0 h1)
  exact (hcomp.const_mul z).congr_deriv (by simp only [kSlice0ww]; ring)

/-- `∂_w kSlice1 = kSlice1w`. -/
theorem hasDerivAt_kSlice1_snd (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (kSlice1 p z) (kSlice1w p z w) w := by
  have hcomp : HasDerivAt (fun v : ℝ => Jp' p (z * v)) (Jp'' (z * w) * z) w :=
    hasDerivAt_comp_mul_left (hasDerivAt_Jp' hp0 hp1 h0 h1)
  exact ((hasDerivAt_id' (x := w)).mul hcomp).congr_deriv (by simp only [kSlice1w]; ring)

/-- `∂_w kSlice1w = kSlice1ww`. -/
theorem hasDerivAt_kSlice1w_snd (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (kSlice1w p z) (kSlice1ww z w) w := by
  have hA : HasDerivAt (fun v : ℝ => Jp' p (z * v)) (Jp'' (z * w) * z) w :=
    hasDerivAt_comp_mul_left (hasDerivAt_Jp' hp0 hp1 h0 h1)
  have hB : HasDerivAt (fun v : ℝ => Jp'' (z * v)) (Jp3 (z * w) * z) w :=
    hasDerivAt_comp_mul_left (hasDerivAt_Jp'' h0 h1)
  have hC : HasDerivAt (fun v : ℝ => v * z * Jp'' (z * v))
      (1 * z * Jp'' (z * w) + w * z * (Jp3 (z * w) * z)) w :=
    ((hasDerivAt_id' (x := w)).mul_const z).mul hB
  exact (hA.add hC).congr_deriv (by simp only [kSlice1ww]; ring)

/-- `∂_w kSlice2 = kSlice2w`. -/
theorem hasDerivAt_kSlice2_snd (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (kSlice2 z) (kSlice2w z w) w := by
  have hB : HasDerivAt (fun v : ℝ => Jp'' (z * v)) (Jp3 (z * w) * z) w :=
    hasDerivAt_comp_mul_left (hasDerivAt_Jp'' h0 h1)
  have hsq : HasDerivAt (fun v : ℝ => v ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
  exact (hsq.mul hB).congr_deriv (by simp only [kSlice2w]; ring)

/-- `∂_w kSlice2w = kSlice2ww`. -/
theorem hasDerivAt_kSlice2w_snd (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (kSlice2w z) (kSlice2ww z w) w := by
  have hB : HasDerivAt (fun v : ℝ => Jp'' (z * v)) (Jp3 (z * w) * z) w :=
    hasDerivAt_comp_mul_left (hasDerivAt_Jp'' h0 h1)
  have hC : HasDerivAt (fun v : ℝ => Jp3 (z * v)) (Jp4 (z * w) * z) w :=
    hasDerivAt_comp_mul_left (hasDerivAt_Jp3 h0 h1)
  have hsq : HasDerivAt (fun v : ℝ => v ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
  have hT1 : HasDerivAt (fun v : ℝ => 2 * v * Jp'' (z * v))
      (2 * Jp'' (z * w) + 2 * w * (Jp3 (z * w) * z)) w := by
    have hlin : HasDerivAt (fun v : ℝ => 2 * v) 2 w := by
      simpa using (hasDerivAt_id' (x := w)).const_mul (2 : ℝ)
    exact hlin.mul hB
  have hT2 : HasDerivAt (fun v : ℝ => v ^ 2 * z * Jp3 (z * v))
      (2 * w * z * Jp3 (z * w) + w ^ 2 * z * (Jp4 (z * w) * z)) w :=
    (hsq.mul_const z).mul hC
  exact (hT1.add hT2).congr_deriv (by simp only [kSlice2ww]; ring)

/-- `∂_z kSlice0 = kSlice1`. -/
theorem hasDerivAt_kSlice0_fst (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (fun ζ : ℝ => kSlice0 p ζ w) (kSlice1 p z w) z := by
  have hcomp : HasDerivAt (fun ζ : ℝ => Jp p (ζ * w)) (Jp' p (z * w) * w) z :=
    hasDerivAt_comp_mul_right (hasDerivAt_Jp hp0 hp1 h0 h1)
  exact hcomp.congr_deriv (by simp only [kSlice1]; ring)

/-- `∂_z kSlice0w = kSlice1w`, one of the two mixed derivatives whose equality
`hasDerivAt_powDD_param` needs at the nodes. -/
theorem hasDerivAt_kSlice0w_fst (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (fun ζ : ℝ => kSlice0w p ζ w) (kSlice1w p z w) z := by
  have hcomp : HasDerivAt (fun ζ : ℝ => Jp' p (ζ * w)) (Jp'' (z * w) * w) z :=
    hasDerivAt_comp_mul_right (hasDerivAt_Jp' hp0 hp1 h0 h1)
  exact ((hasDerivAt_id' (x := z)).mul hcomp).congr_deriv (by simp only [kSlice1w]; ring)

/-- `∂_z kSlice0ww = kSlice1ww`. -/
theorem hasDerivAt_kSlice0ww_fst (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (fun ζ : ℝ => kSlice0ww ζ w) (kSlice1ww z w) z := by
  have hB : HasDerivAt (fun ζ : ℝ => Jp'' (ζ * w)) (Jp3 (z * w) * w) z :=
    hasDerivAt_comp_mul_right (hasDerivAt_Jp'' h0 h1)
  have hsq : HasDerivAt (fun ζ : ℝ => ζ ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  exact (hsq.mul hB).congr_deriv (by simp only [kSlice1ww]; ring)

/-- `∂_z kSlice1 = kSlice2`. -/
theorem hasDerivAt_kSlice1_fst (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (fun ζ : ℝ => kSlice1 p ζ w) (kSlice2 z w) z := by
  have hcomp : HasDerivAt (fun ζ : ℝ => Jp' p (ζ * w)) (Jp'' (z * w) * w) z :=
    hasDerivAt_comp_mul_right (hasDerivAt_Jp' hp0 hp1 h0 h1)
  exact (hcomp.const_mul w).congr_deriv (by simp only [kSlice2]; ring)

/-- `∂_z kSlice1w = kSlice2w`, the second mixed derivative used at the nodes. -/
theorem hasDerivAt_kSlice1w_fst (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (fun ζ : ℝ => kSlice1w p ζ w) (kSlice2w z w) z := by
  have hA : HasDerivAt (fun ζ : ℝ => Jp' p (ζ * w)) (Jp'' (z * w) * w) z :=
    hasDerivAt_comp_mul_right (hasDerivAt_Jp' hp0 hp1 h0 h1)
  have hB : HasDerivAt (fun ζ : ℝ => Jp'' (ζ * w)) (Jp3 (z * w) * w) z :=
    hasDerivAt_comp_mul_right (hasDerivAt_Jp'' h0 h1)
  have hC : HasDerivAt (fun ζ : ℝ => w * ζ * Jp'' (ζ * w))
      (w * 1 * Jp'' (z * w) + w * z * (Jp3 (z * w) * w)) z :=
    ((hasDerivAt_id' (x := z)).const_mul w).mul hB
  exact (hA.add hC).congr_deriv (by simp only [kSlice2w]; ring)

/-- `∂_z kSlice1ww = kSlice2ww`. -/
theorem hasDerivAt_kSlice1ww_fst (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (fun ζ : ℝ => kSlice1ww ζ w) (kSlice2ww z w) z := by
  have hB : HasDerivAt (fun ζ : ℝ => Jp'' (ζ * w)) (Jp3 (z * w) * w) z :=
    hasDerivAt_comp_mul_right (hasDerivAt_Jp'' h0 h1)
  have hC : HasDerivAt (fun ζ : ℝ => Jp3 (ζ * w)) (Jp4 (z * w) * w) z :=
    hasDerivAt_comp_mul_right (hasDerivAt_Jp3 h0 h1)
  have hsq : HasDerivAt (fun ζ : ℝ => ζ ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have hT1 : HasDerivAt (fun ζ : ℝ => 2 * ζ * Jp'' (ζ * w))
      (2 * Jp'' (z * w) + 2 * z * (Jp3 (z * w) * w)) z := by
    have hlin : HasDerivAt (fun ζ : ℝ => 2 * ζ) 2 z := by
      simpa using (hasDerivAt_id' (x := z)).const_mul (2 : ℝ)
    exact hlin.mul hB
  have hT2 : HasDerivAt (fun ζ : ℝ => w * ζ ^ 2 * Jp3 (ζ * w))
      (w * (2 * z) * Jp3 (z * w) + w * z ^ 2 * (Jp4 (z * w) * w)) z :=
    (hsq.const_mul w).mul hC
  exact (hT1.add hT2).congr_deriv (by simp only [kSlice2ww]; ring)

end Table

/-! ## The second chart derivative of the three slices

`thetaV0`, `thetaV1`, `thetaV2` are `powDeriv2` of the derivative chains
`kSlice0 → kSlice0w → kSlice0ww`, `kSlice1 → kSlice1w → kSlice1ww` and
`kSlice2 → kSlice2w → kSlice2ww`; they are exactly the quantities that
`powDD_mem_of_powDeriv2_mem` sandwiches. -/

/-- The second derivative of `K(z,·)` in the chart `v = w^d`. -/
noncomputable def thetaV0 (d : ℕ) (p z w : ℝ) : ℝ :=
  powDeriv2 d (kSlice0w p z) (kSlice0ww z) w

/-- The second derivative of `∂_zK(z,·)` in the chart `v = w^d`. -/
noncomputable def thetaV1 (d : ℕ) (p z w : ℝ) : ℝ :=
  powDeriv2 d (kSlice1w p z) (kSlice1ww z) w

/-- The second derivative of `∂_z²K(z,·)` in the chart `v = w^d`.  It is `p`-free. -/
noncomputable def thetaV2 (d : ℕ) (z w : ℝ) : ℝ :=
  powDeriv2 d (kSlice2w z) (kSlice2ww z) w

/-- The closed form of `thetaV1`. -/
theorem thetaV1_eq (d : ℕ) (p z w : ℝ) :
    thetaV1 d p z w
      = (w * (2 * z * Jp'' (z * w) + w * z ^ 2 * Jp3 (z * w))
          - ((d : ℝ) - 1) * (Jp' p (z * w) + w * z * Jp'' (z * w)))
        / ((d : ℝ) ^ 2 * w ^ (2 * d - 1)) := rfl

/-- The closed form of `thetaV2`. -/
theorem thetaV2_eq (d : ℕ) (z w : ℝ) :
    thetaV2 d z w
      = (w * (2 * Jp'' (z * w) + 4 * w * z * Jp3 (z * w) + w ^ 2 * z ^ 2 * Jp4 (z * w))
          - ((d : ℝ) - 1) * (2 * w * Jp'' (z * w) + w ^ 2 * z * Jp3 (z * w)))
        / ((d : ℝ) ^ 2 * w ^ (2 * d - 1)) := rfl

/-- **The whole `p`-dependence of `thetaV1` is the displacement constant.**  By
`Jp'_eq_Jp'_pStar_add` the first derivative of the entropy moves with `p` by the constant
`Λ_p = ℓ(p) - ℓ(p_*)`, so `thetaV1` moves by `-(d-1)Λ_p/(d²w^{2d-1})` and `thetaV2` does not
move at all.  This is what makes the estimate uniform in `h` without any compactness
argument. -/
theorem thetaV1_sub_pStar {d : ℕ} (hd : 2 ≤ d) {p z w : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h0 : 0 < z * w) (h1 : z * w < 1) :
    thetaV1 d p z w - thetaV1 d (pStar d) z w
      = -(((d : ℝ) - 1) * (ell p - ell (pStar d))) / ((d : ℝ) ^ 2 * w ^ (2 * d - 1)) := by
  rw [thetaV1_eq, thetaV1_eq, Jp'_eq_Jp'_pStar_add hd hp0 hp1 h0 h1, div_sub_div_same]
  congr 1
  ring

/-! ## The corner constant in the chart -/

/-- **The inner operator of the corner, read in the chart.**  For `0 < z < 1`,

  `𝒟_{d,y}J_{p_*}(z·)|_{y=u_*} = (d²u_*^{2d-2}/2)·thetaV0 d p_* z u_*`.

The two `deriv`s of the slice `y ↦ J_{p_*}(zy)` are `kSlice0w` and `kSlice0ww`, and
`powDop_eq_powDeriv2` converts `𝒟_d` into the chart second derivative. -/
theorem powDopOf_kernel_slice_eq_thetaV0 {d : ℕ} (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z)
    (hz1 : z < 1) :
    powDopOf d (fun y => Jp (pStar d) (z * y)) (uStar d)
      = (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) / 2 * thetaV0 d (pStar d) z (uStar d) := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  have hzy : ∀ y ∈ Set.Ioo (0 : ℝ) 1, 0 < z * y ∧ z * y < 1 := by
    intro y hy
    refine ⟨mul_pos hz0 hy.1, ?_⟩
    have h := mul_lt_mul_of_pos_right hz1 hy.1
    linarith [hy.2]
  have hJ : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => Jp (pStar d) (z * v)) (kSlice0w (pStar d) z y) y := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hzy y hy
    exact hasDerivAt_kSlice0_snd hp0 hp1 hy0 hy1
  have humem : uStar d ∈ Set.Ioo (0 : ℝ) 1 := ⟨hu0, hu1⟩
  obtain ⟨hu0', hu1'⟩ := hzy _ humem
  have e1 : deriv (fun v : ℝ => Jp (pStar d) (z * v)) (uStar d)
      = kSlice0w (pStar d) z (uStar d) := (hJ _ humem).deriv
  have hEq : deriv (fun v : ℝ => Jp (pStar d) (z * v)) =ᶠ[𝓝 (uStar d)] kSlice0w (pStar d) z := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with y hy
    exact (hJ y hy).deriv
  have e2 : deriv (deriv fun v : ℝ => Jp (pStar d) (z * v)) (uStar d)
      = kSlice0ww z (uStar d) := by
    rw [hEq.deriv_eq]
    exact (hasDerivAt_kSlice0w_snd hp0 hp1 hu0' hu1').deriv
  rw [powDopOf, powDop_congr d e1 e2, thetaV0]
  exact powDop_eq_powDeriv2 hd _ _ hu0

/-- Differentiating `thetaV0` in the frozen variable gives `thetaV1`. -/
theorem hasDerivAt_thetaV0_fst {d : ℕ} {p z w : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (fun ζ : ℝ => thetaV0 d p ζ w) (thetaV1 d p z w) z := by
  have hA := hasDerivAt_kSlice0ww_fst h0 h1 (z := z) (w := w)
  have hB := hasDerivAt_kSlice0w_fst hp0 hp1 h0 h1 (p := p) (z := z) (w := w)
  exact ((hA.const_mul w).sub (hB.const_mul ((d : ℝ) - 1))).div_const
    ((d : ℝ) ^ 2 * w ^ (2 * d - 1))

/-- Differentiating `thetaV1` in the frozen variable gives `thetaV2`. -/
theorem hasDerivAt_thetaV1_fst {d : ℕ} {p z w : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h0 : 0 < z * w) (h1 : z * w < 1) :
    HasDerivAt (fun ζ : ℝ => thetaV1 d p ζ w) (thetaV2 d z w) z := by
  have hA := hasDerivAt_kSlice1ww_fst h0 h1 (z := z) (w := w)
  have hB := hasDerivAt_kSlice1w_fst hp0 hp1 h0 h1 (p := p) (z := z) (w := w)
  exact ((hA.const_mul w).sub (hB.const_mul ((d : ℝ) - 1))).div_const
    ((d : ℝ) ^ 2 * w ^ (2 * d - 1))

/-- The arithmetic behind `thetaV_theta_value`, isolated from the calculus: both sides are
`X(u c₂ - (d-1)c₁)/(4u)` with `X = d²u^{2d-2}`, once `u^{2d-1} = u^{2d-2}·u` is used. -/
private theorem theta_arith {d : ℕ} {u c1 c2 : ℝ} (hd : 2 ≤ d) (hu : 0 < u)
    (hkey : ((d : ℝ) ^ 2 * u ^ (2 * d - 2) / 2 * c2
        - ((d : ℝ) - 1) / u * ((d : ℝ) ^ 2 * u ^ (2 * d - 2) / 2 * c1)) / 2
      = (d : ℝ) ^ 3 / 4) :
    ((d : ℝ) ^ 2 * u ^ (2 * d - 2)) ^ 2
        * ((u * (c2 / 2) - ((d : ℝ) - 1) * (c1 / 2)) / ((d : ℝ) ^ 2 * u ^ (2 * d - 1))) / 2
      = (d : ℝ) ^ 3 / 4 := by
  have hune : u ≠ 0 := ne_of_gt hu
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hU : u ^ (2 * d - 2) ≠ 0 := pow_ne_zero _ hune
  have hpow : u ^ (2 * d - 1) = u ^ (2 * d - 2) * u := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow, ← hkey]
  field_simp

/-- **The corner constant, in the chart.**  With `c₁ = thetaV1 d p_* u_* u_*` and
`c₂ = thetaV2 d u_* u_*`,

  `(d²u_*^{2d-2})² · ((u_*(c₂/2) - (d-1)(c₁/2))/(d²u_*^{2d-1})) / 2 = d³/4`.

The left-hand side is the value the two mean-value steps of `exists_kernelTheta_error`
converge to: the outer `mfac·mfac`, the outer chart second derivative `powDeriv2` of the pair
`(thetaV1, thetaV2)`, and the two halves of the two sandwiches.  The proof reads
`powDopOf_powDopOf_kernel` through `powDopOf_kernel_slice_eq_thetaV0` and its two
derivatives, `powDop_eq_powDeriv2` supplying the factor `d²u_*^{2d-2}/2` once per chart. -/
theorem thetaV_theta_value {d : ℕ} (hd : 2 ≤ d) :
    ((d : ℝ) ^ 2 * uStar d ^ (2 * d - 2)) ^ 2
        * ((uStar d * (thetaV2 d (uStar d) (uStar d) / 2)
            - ((d : ℝ) - 1) * (thetaV1 d (pStar d) (uStar d) (uStar d) / 2))
          / ((d : ℝ) ^ 2 * uStar d ^ (2 * d - 1))) / 2
      = (d : ℝ) ^ 3 / 4 := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  -- the products of two window points stay inside `(0,1)`
  have hprod : ∀ z ∈ Set.Ioo (0 : ℝ) 1, 0 < z * uStar d ∧ z * uStar d < 1 := by
    intro z hz
    refine ⟨mul_pos hz.1 hu0, ?_⟩
    have h := mul_lt_mul_of_pos_right hz.2 hu0
    linarith
  obtain ⟨huu0, huu1⟩ := hprod _ ⟨hu0, hu1⟩
  -- the inner operator, as a function of the frozen variable
  have hG : (fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d))
      =ᶠ[𝓝 (uStar d)] fun x =>
        (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) / 2 * thetaV0 d (pStar d) x (uStar d) := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with x hx
    exact powDopOf_kernel_slice_eq_thetaV0 hd hx.1 hx.2
  have hder1 : deriv (fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d))
      =ᶠ[𝓝 (uStar d)] fun x =>
        (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) / 2 * thetaV1 d (pStar d) x (uStar d) := by
    filter_upwards [hG.deriv, Ioo_mem_nhds hu0 hu1] with x hx hxm
    obtain ⟨hx0, hx1⟩ := hprod x hxm
    rw [hx]
    exact ((hasDerivAt_thetaV0_fst hp0 hp1 hx0 hx1).const_mul _).deriv
  have e1 : deriv (fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d)) (uStar d)
      = (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) / 2
        * thetaV1 d (pStar d) (uStar d) (uStar d) := hder1.self_of_nhds
  have e2 : deriv (deriv fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d)) (uStar d)
      = (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) / 2 * thetaV2 d (uStar d) (uStar d) := by
    rw [hder1.deriv_eq]
    exact ((hasDerivAt_thetaV1_fst hp0 hp1 huu0 huu1).const_mul _).deriv
  have hkey : powDop d
        (fun _ : ℝ => (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) / 2
          * thetaV1 d (pStar d) (uStar d) (uStar d))
        (fun _ : ℝ => (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) / 2 * thetaV2 d (uStar d) (uStar d))
        (uStar d)
      = (d : ℝ) ^ 3 / 4 :=
    calc powDop d
          (fun _ : ℝ => (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) / 2
            * thetaV1 d (pStar d) (uStar d) (uStar d))
          (fun _ : ℝ => (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) / 2 * thetaV2 d (uStar d) (uStar d))
          (uStar d)
        = powDop d (deriv fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d))
            (deriv (deriv fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d)))
            (uStar d) := (powDop_congr d e1 e2).symm
      _ = powDopOf d (fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d))
            (uStar d) := rfl
      _ = (d : ℝ) ^ 3 / 4 := powDopOf_powDopOf_kernel hd
  rw [powDop] at hkey
  exact theta_arith hd hu0 hkey

/-! ## The two continuity inputs, and the elementary `ε`-bookkeeping -/

/-- A `ContinuousAt` statement, read as an `ε`-`δ` bound.  The ambient space is a metric
space so that the three instances below — one real variable, a pair and a triple — are all
covered by one lemma. -/
private theorem exists_delta_le {X : Type*} [PseudoMetricSpace X] {F : X → ℝ} {a : X}
    (hF : ContinuousAt F a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, dist x a < δ → |F x - F a| ≤ ε := by
  have hev : ∀ᶠ x in 𝓝 a, dist (F x) (F a) < ε := Metric.tendsto_nhds.mp hF ε hε
  obtain ⟨δ, hδ, hprop⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have h := hprop hx
  rw [Real.dist_eq] at h
  exact h.le

/-- The sandwich `(c-e)/2 ≤ q ≤ (c+e)/2` read as the deviation bound `|q - c/2| ≤ e/2`.  Both
mean-value steps below are used in exactly this way. -/
private theorem abs_sub_half_le {q c e : ℝ} (h1 : (c - e) / 2 ≤ q) (h2 : q ≤ (c + e) / 2) :
    |q - c / 2| ≤ e / 2 := by
  rw [abs_le]
  constructor <;> linarith

/-- `thetaV1` is jointly continuous in the two variables at any interior point of the
domain. -/
private theorem continuousAt_thetaV1 {d : ℕ} {p z w : ℝ} (hd : 2 ≤ d) (hp0 : 0 < p)
    (hp1 : p < 1) (hw : 0 < w) (h0 : 0 < z * w) (h1 : z * w < 1) :
    ContinuousAt (fun q : ℝ × ℝ => thetaV1 d p q.1 q.2) (z, w) := by
  have hfst : ContinuousAt (fun q : ℝ × ℝ => q.1) (z, w) := continuous_fst.continuousAt
  have hsnd : ContinuousAt (fun q : ℝ × ℝ => q.2) (z, w) := continuous_snd.continuousAt
  have hmul : ContinuousAt (fun q : ℝ × ℝ => q.1 * q.2) (z, w) := hfst.mul hsnd
  have cJ1 : ContinuousAt (fun q : ℝ × ℝ => Jp' p (q.1 * q.2)) (z, w) :=
    ContinuousAt.comp (g := Jp' p) (f := fun q : ℝ × ℝ => q.1 * q.2)
      (hasDerivAt_Jp' hp0 hp1 h0 h1).continuousAt hmul
  have cJ2 : ContinuousAt (fun q : ℝ × ℝ => Jp'' (q.1 * q.2)) (z, w) :=
    ContinuousAt.comp (g := Jp'') (f := fun q : ℝ × ℝ => q.1 * q.2)
      (hasDerivAt_Jp'' h0 h1).continuousAt hmul
  have cJ3 : ContinuousAt (fun q : ℝ × ℝ => Jp3 (q.1 * q.2)) (z, w) :=
    ContinuousAt.comp (g := Jp3) (f := fun q : ℝ × ℝ => q.1 * q.2)
      (hasDerivAt_Jp3 h0 h1).continuousAt hmul
  have hne : ((d : ℝ) ^ 2 * w ^ (2 * d - 1)) ≠ 0 :=
    ne_of_gt (mul_pos (pow_pos (dpos hd) 2) (pow_pos hw _))
  simp only [thetaV1_eq]
  exact ((hsnd.mul (((continuousAt_const.mul hfst).mul cJ2).add
      ((hsnd.mul (hfst.pow 2)).mul cJ3))).sub
    (continuousAt_const.mul (cJ1.add ((hsnd.mul hfst).mul cJ2)))).div
    (continuousAt_const.mul (hsnd.pow _)) hne

/-- `thetaV2` is jointly continuous in the two variables at any interior point of the
domain.  It carries no `p`. -/
private theorem continuousAt_thetaV2 {d : ℕ} {z w : ℝ} (hd : 2 ≤ d) (hw : 0 < w)
    (h0 : 0 < z * w) (h1 : z * w < 1) :
    ContinuousAt (fun q : ℝ × ℝ => thetaV2 d q.1 q.2) (z, w) := by
  have hfst : ContinuousAt (fun q : ℝ × ℝ => q.1) (z, w) := continuous_fst.continuousAt
  have hsnd : ContinuousAt (fun q : ℝ × ℝ => q.2) (z, w) := continuous_snd.continuousAt
  have hmul : ContinuousAt (fun q : ℝ × ℝ => q.1 * q.2) (z, w) := hfst.mul hsnd
  have cJ2 : ContinuousAt (fun q : ℝ × ℝ => Jp'' (q.1 * q.2)) (z, w) :=
    ContinuousAt.comp (g := Jp'') (f := fun q : ℝ × ℝ => q.1 * q.2)
      (hasDerivAt_Jp'' h0 h1).continuousAt hmul
  have cJ3 : ContinuousAt (fun q : ℝ × ℝ => Jp3 (q.1 * q.2)) (z, w) :=
    ContinuousAt.comp (g := Jp3) (f := fun q : ℝ × ℝ => q.1 * q.2)
      (hasDerivAt_Jp3 h0 h1).continuousAt hmul
  have cJ4 : ContinuousAt (fun q : ℝ × ℝ => Jp4 (q.1 * q.2)) (z, w) :=
    ContinuousAt.comp (g := Jp4) (f := fun q : ℝ × ℝ => q.1 * q.2)
      (hasDerivAt_Jp4 h0 h1).continuousAt hmul
  have hne : ((d : ℝ) ^ 2 * w ^ (2 * d - 1)) ≠ 0 :=
    ne_of_gt (mul_pos (pow_pos (dpos hd) 2) (pow_pos hw _))
  simp only [thetaV2_eq]
  exact ((hsnd.mul (((continuousAt_const.mul cJ2).add
      (((continuousAt_const.mul hsnd).mul hfst).mul cJ3)).add
      (((hsnd.pow 2).mul (hfst.pow 2)).mul cJ4))).sub
    (continuousAt_const.mul (((continuousAt_const.mul hsnd).mul cJ2).add
      (((hsnd.pow 2).mul hfst).mul cJ3)))).div
    (continuousAt_const.mul (hsnd.pow _)) hne

/-- **The outer chart second derivative, as a function of three scalars.**  `powDeriv2 d φ₁ φ₂`
at `z` reads `φ₁` and `φ₂` only at `z`, so the second mean-value step is a continuous function
of the point and of the two values the first step produces. -/
noncomputable def outerQ (d : ℕ) (z a b : ℝ) : ℝ :=
  (z * b - ((d : ℝ) - 1) * a) / ((d : ℝ) ^ 2 * z ^ (2 * d - 1))

/-- `powDeriv2` is `outerQ` at the two values of the derivative pair. -/
theorem powDeriv2_eq_outerQ (d : ℕ) (phi1 phi2 : ℝ → ℝ) (z : ℝ) :
    powDeriv2 d phi1 phi2 z = outerQ d z (phi1 z) (phi2 z) := rfl

/-- `outerQ` is jointly continuous in its three arguments away from `z = 0`. -/
private theorem continuousAt_outerQ {d : ℕ} (hd : 2 ≤ d) {z : ℝ} (hz : 0 < z) (a b : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ => outerQ d q.1 q.2.1 q.2.2) (z, a, b) := by
  have hne : ((d : ℝ) ^ 2 * z ^ (2 * d - 1)) ≠ 0 :=
    ne_of_gt (mul_pos (pow_pos (dpos hd) 2) (pow_pos hz _))
  have h1 : ContinuousAt (fun q : ℝ × ℝ × ℝ => q.1) (z, a, b) := continuous_fst.continuousAt
  have h2 : ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.1) (z, a, b) :=
    continuous_snd.fst.continuousAt
  have h3 : ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.2) (z, a, b) :=
    continuous_snd.snd.continuousAt
  simp only [outerQ]
  exact ((h1.mul h3).sub (continuousAt_const.mul h2)).div
    (continuousAt_const.mul (h1.pow _)) hne

/-- **A bound on the chart second derivative from bounds on the derivative pair.**
`powDeriv2 d φ₁ φ₂` reads its two arguments only at the evaluation point, so bounds there
together with the window bound it.  This is the second-order companion of `abs_powDeriv_le`
(`SingularEndpoint/AuxiliaryLagrangian/PowFirstOrder.lean`), and it is what the window bounds on `u_{0,h}`, `u_{d,h}`
consume. -/
theorem abs_powDeriv2_le {d : ℕ} (hd : 2 ≤ d) {phi1 phi2 : ℝ → ℝ} {A Bb C1 C2 x : ℝ}
    (hA : 0 < A) (hx : x ∈ Set.Icc A Bb) (h1 : |phi1 x| ≤ C1) (h2 : |phi2 x| ≤ C2) :
    |powDeriv2 d phi1 phi2 x|
      ≤ (Bb * C2 + ((d : ℝ) - 1) * C1) / ((d : ℝ) ^ 2 * A ^ (2 * d - 1)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hd1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hx0 : 0 < x := lt_of_lt_of_le hA hx.1
  have hC1 : 0 ≤ C1 := le_trans (abs_nonneg _) h1
  have hC2 : 0 ≤ C2 := le_trans (abs_nonneg _) h2
  have hBb : 0 < Bb := lt_of_lt_of_le hx0 hx.2
  have hden : (0 : ℝ) < (d : ℝ) ^ 2 * x ^ (2 * d - 1) :=
    mul_pos (pow_pos hdpos 2) (pow_pos hx0 _)
  have hden0 : (0 : ℝ) < (d : ℝ) ^ 2 * A ^ (2 * d - 1) :=
    mul_pos (pow_pos hdpos 2) (pow_pos hA _)
  have hdenle : (d : ℝ) ^ 2 * A ^ (2 * d - 1) ≤ (d : ℝ) ^ 2 * x ^ (2 * d - 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA.le hx.1 _) (le_of_lt (pow_pos hdpos 2))
  have hnum : |x * phi2 x - ((d : ℝ) - 1) * phi1 x| ≤ Bb * C2 + ((d : ℝ) - 1) * C1 := by
    have htri := abs_add_le (x * phi2 x) (-(((d : ℝ) - 1) * phi1 x))
    rw [← sub_eq_add_neg, abs_neg] at htri
    have hA1 : |x * phi2 x| ≤ Bb * C2 := by
      rw [abs_mul, abs_of_pos hx0]
      exact mul_le_mul hx.2 h2 (abs_nonneg _) hBb.le
    have hA2 : |((d : ℝ) - 1) * phi1 x| ≤ ((d : ℝ) - 1) * C1 := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < (d : ℝ) - 1 by linarith)]
      exact mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith
  have hN0 : (0 : ℝ) ≤ Bb * C2 + ((d : ℝ) - 1) * C1 := by
    have hp1 : (0 : ℝ) ≤ Bb * C2 := mul_nonneg hBb.le hC2
    have hp2 : (0 : ℝ) ≤ ((d : ℝ) - 1) * C1 := mul_nonneg (by linarith) hC1
    linarith
  rw [powDeriv2, abs_div, abs_of_pos hden, div_le_div_iff₀ hden hden0]
  calc |x * phi2 x - ((d : ℝ) - 1) * phi1 x| * ((d : ℝ) ^ 2 * A ^ (2 * d - 1))
      ≤ (Bb * C2 + ((d : ℝ) - 1) * C1) * ((d : ℝ) ^ 2 * A ^ (2 * d - 1)) :=
        mul_le_mul_of_nonneg_right hnum hden0.le
    _ ≤ (Bb * C2 + ((d : ℝ) - 1) * C1) * ((d : ℝ) ^ 2 * x ^ (2 * d - 1)) :=
        mul_le_mul_of_nonneg_left hdenle hN0

namespace KKTFamily

variable {d : ℕ}

/-! ## The inner divided difference as a function of the frozen variable -/

/-- **The inner divided difference of the corner**, as a function of the frozen first
variable: `z ↦ powDD_w K_h(z,·)` evaluated at `y`.  `kernelTheta_eq` writes `Θ_h` as
`mfac·mfac` times the `powDD` of this function. -/
noncomputable def thetaSlice (B : KKTFamily d) (h y z : ℝ) : ℝ :=
  powDD d (kSlice0 (B.p h) z) (B.sVal h) (B.tVal h) y

/-- The derivative of `thetaSlice` in the frozen variable
(`KKTFamily.hasDerivAt_thetaSlice`). -/
noncomputable def thetaSlice1 (B : KKTFamily d) (h y z : ℝ) : ℝ :=
  powDD d (kSlice1 (B.p h) z) (B.sVal h) (B.tVal h) y

/-- The second derivative of `thetaSlice` in the frozen variable
(`KKTFamily.hasDerivAt_thetaSlice1`). -/
noncomputable def thetaSlice2 (B : KKTFamily d) (h y z : ℝ) : ℝ :=
  powDD d (kSlice2 z) (B.sVal h) (B.tVal h) y

/-- `Θ_h(x,y)` is `mfac(x)·mfac(y)` times the divided difference of `thetaSlice`.  This is
the definition of `KKTFamily.kernelTheta` with the kernel written as a `kSlice0`. -/
theorem kernelTheta_eq (B : KKTFamily d) (h x y : ℝ) :
    B.kernelTheta h x y
      = mfac d (B.sVal h) (B.tVal h) x * mfac d (B.sVal h) (B.tVal h) y
        * powDD d (B.thetaSlice h y) (B.sVal h) (B.tVal h) x := rfl

/-- The product of two points of the family window stays in `(0,1)`; the elementary
hypothesis every derivative of the table needs. -/
private theorem mul_mem_Ioo_of_mem {A Bb z w : ℝ} (hA : 0 < A) (hBb : Bb * Bb < 1)
    (hz : z ∈ Set.Icc A Bb) (hw : w ∈ Set.Icc A Bb) : 0 < z * w ∧ z * w < 1 := by
  have hz0 : 0 < z := lt_of_lt_of_le hA hz.1
  have hw0 : 0 < w := lt_of_lt_of_le hA hw.1
  refine ⟨mul_pos hz0 hw0, lt_of_le_of_lt ?_ hBb⟩
  exact mul_le_mul hz.2 hw.2 hw0.le (le_trans hz0.le hz.2)

/-- **The derivative of the inner divided difference in the frozen variable.**  This is
`hasDerivAt_powDD_param` at the kernel table: the parameter derivatives are
`hasDerivAt_kSlice0_fst`, `hasDerivAt_kSlice0w_fst`, the free-variable derivatives at the two
nodes are `hasDerivAt_kSlice0_snd`, `hasDerivAt_kSlice1_snd`, and the two mixed derivatives
agree because both are computed in closed form. -/
theorem hasDerivAt_thetaSlice (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) {A Bb y z : ℝ} (hA : 0 < A) (hBb : Bb * Bb < 1)
    (hs : B.sVal h ∈ Set.Icc A Bb) (ht : B.tVal h ∈ Set.Icc A Bb)
    (hy : y ∈ Set.Icc A Bb) (hz : z ∈ Set.Icc A Bb) :
    HasDerivAt (B.thetaSlice h y) (B.thetaSlice1 h y z) z := by
  have hp := B.p_mem h hh
  have hsp : 0 < B.sVal h := lt_of_lt_of_le hA hs.1
  have htp : 0 < B.tVal h := lt_of_lt_of_le hA ht.1
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  obtain ⟨hzs0, hzs1⟩ := mul_mem_Ioo_of_mem hA hBb hz hs
  obtain ⟨hzt0, hzt1⟩ := mul_mem_Ioo_of_mem hA hBb hz ht
  obtain ⟨hzy0, hzy1⟩ := mul_mem_Ioo_of_mem hA hBb hz hy
  have hev : ∀ c : ℝ, 0 < z * c → z * c < 1 → ∀ᶠ ζ in 𝓝 z, 0 < ζ * c ∧ ζ * c < 1 := by
    intro c h0 h1
    have hcont : ContinuousAt (fun ζ : ℝ => ζ * c) z :=
      (continuous_id.mul continuous_const).continuousAt
    filter_upwards [hcont.preimage_mem_nhds (Ioo_mem_nhds h0 h1)] with ζ hζ
    exact ⟨hζ.1, hζ.2⟩
  refine hasDerivAt_powDD_param (d := d) (f := kSlice0 (B.p h)) (g := kSlice1 (B.p h))
    (fv := kSlice0w (B.p h)) (gv := kSlice1w (B.p h)) (by omega) hsp htp
    (le_trans hA.le hy.1) hst (hasDerivAt_kSlice0_fst hp.1 hp.2 hzs0 hzs1)
    (hasDerivAt_kSlice0_fst hp.1 hp.2 hzt0 hzt1)
    (hasDerivAt_kSlice0_fst hp.1 hp.2 hzy0 hzy1)
    (hasDerivAt_kSlice0w_fst hp.1 hp.2 hzs0 hzs1)
    (hasDerivAt_kSlice0w_fst hp.1 hp.2 hzt0 hzt1) ?_ ?_
    (hasDerivAt_kSlice1_snd hp.1 hp.2 hzs0 hzs1) (hasDerivAt_kSlice1_snd hp.1 hp.2 hzt0 hzt1)
  · filter_upwards [hev _ hzs0 hzs1] with ζ hζ
    exact hasDerivAt_kSlice0_snd hp.1 hp.2 hζ.1 hζ.2
  · filter_upwards [hev _ hzt0 hzt1] with ζ hζ
    exact hasDerivAt_kSlice0_snd hp.1 hp.2 hζ.1 hζ.2

/-- **The second derivative of the inner divided difference in the frozen variable**, the same
argument one step further along the table. -/
theorem hasDerivAt_thetaSlice1 (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) {A Bb y z : ℝ} (hA : 0 < A) (hBb : Bb * Bb < 1)
    (hs : B.sVal h ∈ Set.Icc A Bb) (ht : B.tVal h ∈ Set.Icc A Bb)
    (hy : y ∈ Set.Icc A Bb) (hz : z ∈ Set.Icc A Bb) :
    HasDerivAt (B.thetaSlice1 h y) (B.thetaSlice2 h y z) z := by
  have hp := B.p_mem h hh
  have hsp : 0 < B.sVal h := lt_of_lt_of_le hA hs.1
  have htp : 0 < B.tVal h := lt_of_lt_of_le hA ht.1
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  obtain ⟨hzs0, hzs1⟩ := mul_mem_Ioo_of_mem hA hBb hz hs
  obtain ⟨hzt0, hzt1⟩ := mul_mem_Ioo_of_mem hA hBb hz ht
  obtain ⟨hzy0, hzy1⟩ := mul_mem_Ioo_of_mem hA hBb hz hy
  have hev : ∀ c : ℝ, 0 < z * c → z * c < 1 → ∀ᶠ ζ in 𝓝 z, 0 < ζ * c ∧ ζ * c < 1 := by
    intro c h0 h1
    have hcont : ContinuousAt (fun ζ : ℝ => ζ * c) z :=
      (continuous_id.mul continuous_const).continuousAt
    filter_upwards [hcont.preimage_mem_nhds (Ioo_mem_nhds h0 h1)] with ζ hζ
    exact ⟨hζ.1, hζ.2⟩
  refine hasDerivAt_powDD_param (d := d) (f := kSlice1 (B.p h)) (g := kSlice2)
    (fv := kSlice1w (B.p h)) (gv := kSlice2w) (by omega) hsp htp
    (le_trans hA.le hy.1) hst (hasDerivAt_kSlice1_fst hp.1 hp.2 hzs0 hzs1)
    (hasDerivAt_kSlice1_fst hp.1 hp.2 hzt0 hzt1)
    (hasDerivAt_kSlice1_fst hp.1 hp.2 hzy0 hzy1)
    (hasDerivAt_kSlice1w_fst hp.1 hp.2 hzs0 hzs1)
    (hasDerivAt_kSlice1w_fst hp.1 hp.2 hzt0 hzt1) ?_ ?_
    (hasDerivAt_kSlice2_snd hzs0 hzs1) (hasDerivAt_kSlice2_snd hzt0 hzt1)
  · filter_upwards [hev _ hzs0 hzs1] with ζ hζ
    exact hasDerivAt_kSlice1_snd hp.1 hp.2 hζ.1 hζ.2
  · filter_upwards [hev _ hzt0 hzt1] with ζ hζ
    exact hasDerivAt_kSlice1_snd hp.1 hp.2 hζ.1 hζ.2

/-! ## The two inner sandwiches -/

/-- **The first inner sandwich.**  For every frozen `z` in the window, `thetaSlice1` is
trapped between the halves of the two bounds on `thetaV1` — this is
`powDD_mem_of_powDeriv2_mem` applied to the chain `kSlice1 → kSlice1w → kSlice1ww`, whose
chart second derivative *is* `thetaV1`. -/
theorem thetaSlice1_mem (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) {A Bb m M y z : ℝ} (hA : 0 < A) (hBb : Bb * Bb < 1)
    (hs : B.sVal h ∈ Set.Icc A Bb) (ht : B.tVal h ∈ Set.Icc A Bb) (hy : y ∈ Set.Icc A Bb)
    (hz : z ∈ Set.Icc A Bb)
    (hm : ∀ w ∈ Set.Icc A Bb, m ≤ thetaV1 d (B.p h) z w)
    (hM : ∀ w ∈ Set.Icc A Bb, thetaV1 d (B.p h) z w ≤ M) :
    m / 2 ≤ B.thetaSlice1 h y z ∧ B.thetaSlice1 h y z ≤ M / 2 := by
  have hp := B.p_mem h hh
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  exact powDD_mem_of_powDeriv2_mem hd hA
    (fun w hw => hasDerivAt_kSlice1_snd hp.1 hp.2 (mul_mem_Ioo_of_mem hA hBb hz hw).1
      (mul_mem_Ioo_of_mem hA hBb hz hw).2)
    (fun w hw => hasDerivAt_kSlice1w_snd hp.1 hp.2 (mul_mem_Ioo_of_mem hA hBb hz hw).1
      (mul_mem_Ioo_of_mem hA hBb hz hw).2)
    hm hM hs ht hst hy

/-- **The second inner sandwich**, the same statement for `thetaSlice2` and `thetaV2`.  No
hypothesis on the density is needed: from `J_p''` onwards the entropy derivatives are
`p`-free. -/
theorem thetaSlice2_mem (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hpos : 0 < h)
    {A Bb m M y z : ℝ} (hA : 0 < A) (hBb : Bb * Bb < 1)
    (hs : B.sVal h ∈ Set.Icc A Bb) (ht : B.tVal h ∈ Set.Icc A Bb) (hy : y ∈ Set.Icc A Bb)
    (hz : z ∈ Set.Icc A Bb)
    (hm : ∀ w ∈ Set.Icc A Bb, m ≤ thetaV2 d z w)
    (hM : ∀ w ∈ Set.Icc A Bb, thetaV2 d z w ≤ M) :
    m / 2 ≤ B.thetaSlice2 h y z ∧ B.thetaSlice2 h y z ≤ M / 2 := by
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  exact powDD_mem_of_powDeriv2_mem hd hA
    (fun w hw => hasDerivAt_kSlice2_snd (mul_mem_Ioo_of_mem hA hBb hz hw).1
      (mul_mem_Ioo_of_mem hA hBb hz hw).2)
    (fun w hw => hasDerivAt_kSlice2w_snd (mul_mem_Ioo_of_mem hA hBb hz hw).1
      (mul_mem_Ioo_of_mem hA hBb hz hw).2)
    hm hM hs ht hst hy

/-! ## The corner error of `lem:central-kernel-bound` -/

/-- **The corner error of `lem:central-kernel-bound`**, stated
unwound: for every `ε > 0` there are a window radius `ρ > 0` and a threshold `h_ρ > 0` such
that

  `|Θ_h(x,y) - d³/4| ≤ ε`   for all `0 < h < h_ρ` and all `x, y ∈ 𝓝_ρ`.

This is the paper's `sup_{0<h<h_ρ}‖Θ_h - d³/4‖_{L^∞(𝒩_ρ²)} ≤ a/4` with the supremum unwound
and an arbitrary accuracy in place of `a/4`, and it is exactly what the
quantitative half of `lem:auxiliary-lagrangian-bound` consumes.

The proof is the two mean-value steps of `SingularEndpoint/AuxiliaryLagrangian/PowInterp.lean` applied in the two
variables, joined by the parameter derivative `hasDerivAt_powDD_param`.  The inner step traps
`thetaSlice1`, `thetaSlice2` near `thetaV1`, `thetaV2` at the corner; the outer step traps
the whole divided difference near `outerQ` of those two values; the geometric cofactor `mfac`
is bounded by `mfac_mem_Icc`; and `thetaV_theta_value` identifies the limit with `d³/4`.
The `h`-dependence enters only through `thetaV1_sub_pStar`, i.e. through the constant
`Λ_h = ℓ(p_h) - ℓ(p_*)`. -/
theorem exists_kernelTheta_error (hd : 2 ≤ d) (B : KKTFamily d) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∃ hρ : ℝ, 0 < hρ ∧ ∀ h : ℝ, 0 < h → h < hρ →
      ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
        |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4| ≤ ε := by
  intro ε hε
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hd1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hcor0 : 0 < uStar d * uStar d := mul_pos hu0 hu0
  have hcor1 : uStar d * uStar d < 1 := by nlinarith [hu0, hu1]
  -- the outer product `m₁·m₂·q`
  have hRcont : ContinuousAt (fun q : ℝ × ℝ × ℝ => q.1 * q.2.1 * q.2.2)
      ((d : ℝ) ^ 2 * uStar d ^ (2 * d - 2), (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2),
        outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
          (thetaV2 d (uStar d) (uStar d) / 2) / 2) :=
    ((continuous_fst.mul continuous_snd.fst).mul continuous_snd.snd).continuousAt
  obtain ⟨δR, hδR, hR⟩ := exists_delta_le hRcont hε
  -- the outer chart second derivative
  obtain ⟨δQ, hδQ, hQ⟩ := exists_delta_le
    (continuousAt_outerQ hd hu0 (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
      (thetaV2 d (uStar d) (uStar d) / 2)) (half_pos hδR)
  -- the two inner chart second derivatives
  obtain ⟨ρ1, hρ1, hV1⟩ := exists_delta_le
    (continuousAt_thetaV1 hd hp0 hp1 hu0 hcor0 hcor1) (half_pos (half_pos hδQ))
  obtain ⟨ρ2, hρ2, hV2⟩ := exists_delta_le
    (continuousAt_thetaV2 hd hu0 hcor0 hcor1) (half_pos hδQ)
  -- the geometric cofactor
  obtain ⟨ρ3, hρ3, hMf⟩ := exists_delta_le
    (F := fun r : ℝ => (d : ℝ) ^ 2 * r ^ (2 * d - 2)) (a := uStar d)
    (continuous_const.mul (continuous_pow (2 * d - 2))).continuousAt (half_pos hδR)
  -- the window radius
  obtain ⟨ρ, hρpos, hb1, hb2, hb3, hb4, hb5, hb6⟩ :
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ1 ∧ ρ < ρ2 ∧ ρ < ρ3 ∧ ρ < δQ ∧ ρ ≤ uStar d / 2 ∧
        ρ ≤ (1 - uStar d) / 2 := by
    have hm : 0 < min (min ρ1 (min ρ2 ρ3))
        (min δQ (min (uStar d / 2) ((1 - uStar d) / 2))) :=
      lt_min (lt_min hρ1 (lt_min hρ2 hρ3))
        (lt_min hδQ (lt_min (by linarith only [hu0]) (by linarith only [hu1])))
    have ha1 : min (min ρ1 (min ρ2 ρ3))
        (min δQ (min (uStar d / 2) ((1 - uStar d) / 2))) ≤ ρ1 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have ha2 : min (min ρ1 (min ρ2 ρ3))
        (min δQ (min (uStar d / 2) ((1 - uStar d) / 2))) ≤ ρ2 :=
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have ha3 : min (min ρ1 (min ρ2 ρ3))
        (min δQ (min (uStar d / 2) ((1 - uStar d) / 2))) ≤ ρ3 :=
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have ha4 : min (min ρ1 (min ρ2 ρ3))
        (min δQ (min (uStar d / 2) ((1 - uStar d) / 2))) ≤ δQ :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have ha5 : min (min ρ1 (min ρ2 ρ3))
        (min δQ (min (uStar d / 2) ((1 - uStar d) / 2))) ≤ uStar d / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have ha6 : min (min ρ1 (min ρ2 ρ3))
        (min δQ (min (uStar d / 2) ((1 - uStar d) / 2))) ≤ (1 - uStar d) / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    exact ⟨min (min ρ1 (min ρ2 ρ3)) (min δQ (min (uStar d / 2) ((1 - uStar d) / 2))) / 2,
      by linarith only [hm], by linarith only [hm, ha1], by linarith only [hm, ha2],
      by linarith only [hm, ha3], by linarith only [hm, ha4], by linarith only [hm, ha5],
      by linarith only [hm, ha6]⟩
  refine ⟨ρ, hρpos, ?_⟩
  -- the window, and the two structural facts about it
  have hA : 0 < uStar d - ρ := by linarith only [hu0, hb5]
  have hBb0 : (0 : ℝ) < uStar d + ρ := by linarith only [hu0, hρpos]
  have hBb1 : uStar d + ρ < 1 := by linarith only [hu1, hb6]
  have hBbsq : (uStar d + ρ) * (uStar d + ρ) < 1 := by nlinarith [hBb0, hBb1]
  -- the `h`-thresholds
  obtain ⟨δa, hδa, hatoms⟩ := exists_atoms_mem_centralWindow B hρpos
  obtain ⟨δe, hδe, hell⟩ := exists_delta_le (ell_p_continuousAt hd B)
    (show (0 : ℝ) < δQ / 4 * (d : ℝ) * (uStar d - ρ) ^ (2 * d - 1) from
      mul_pos (mul_pos (by linarith only [hδQ]) hdpos) (pow_pos hA _))
  refine ⟨min (min δa δe) B.h₀, lt_min (lt_min hδa hδe) B.h₀_pos, ?_⟩
  intro h hh0 hhb x hx y hy
  have hhδa : h < δa := lt_of_lt_of_le hhb (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhδe : h < δe := lt_of_lt_of_le hhb (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhh : |h| < B.h₀ := by
    rw [abs_of_pos hh0]
    exact lt_of_lt_of_le hhb (min_le_right _ _)
  have hp := B.p_mem h hhh
  obtain ⟨hsmem, htmem⟩ := hatoms h hh0 hhδa
  have hs : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hsmem
  have ht : B.tVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := htmem
  have hx' : x ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hx
  have hy' : y ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hy
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  -- the displacement of the density
  have hLam : |ell (B.p h) - ell (pStar d)|
      ≤ δQ / 4 * (d : ℝ) * (uStar d - ρ) ^ (2 * d - 1) := by
    have hstep := hell h (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
      exact hhδe)
    rwa [B.p_zero] at hstep
  -- the distance of `thetaV1` from its corner value, uniformly in `h`
  have hV1h : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ), ∀ w ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |thetaV1 d (B.p h) z w - thetaV1 d (pStar d) (uStar d) (uStar d)| ≤ δQ / 2 := by
    intro z hz w hw
    obtain ⟨hzw0, hzw1⟩ := mul_mem_Ioo_of_mem hA hBbsq hz hw
    have hw0 : 0 < w := lt_of_lt_of_le hA hw.1
    have hwpow : (uStar d - ρ) ^ (2 * d - 1) ≤ w ^ (2 * d - 1) :=
      pow_le_pow_left₀ hA.le hw.1 _
    have hden : (0 : ℝ) < (d : ℝ) ^ 2 * w ^ (2 * d - 1) :=
      mul_pos (pow_pos hdpos 2) (pow_pos hw0 _)
    have hshift : |thetaV1 d (B.p h) z w - thetaV1 d (pStar d) z w| ≤ δQ / 4 := by
      rw [thetaV1_sub_pStar hd hp.1 hp.2 hzw0 hzw1, abs_div, abs_neg, abs_mul,
        abs_of_pos hden, div_le_iff₀ hden,
        abs_of_pos (show (0 : ℝ) < (d : ℝ) - 1 by linarith only [hd1])]
      have hstep : ((d : ℝ) - 1) * |ell (B.p h) - ell (pStar d)|
          ≤ ((d : ℝ) - 1) * (δQ / 4 * (d : ℝ) * (uStar d - ρ) ^ (2 * d - 1)) :=
        mul_le_mul_of_nonneg_left hLam (by linarith only [hd1])
      have hfac : ((d : ℝ) - 1) * (δQ / 4 * (d : ℝ) * (uStar d - ρ) ^ (2 * d - 1))
          = δQ / 4 * (uStar d - ρ) ^ (2 * d - 1) * (((d : ℝ) - 1) * (d : ℝ)) := by ring
      have hfac2 : δQ / 4 * ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1))
          = δQ / 4 * (uStar d - ρ) ^ (2 * d - 1) * ((d : ℝ) ^ 2) := by ring
      have hnn : (0 : ℝ) ≤ δQ / 4 * (uStar d - ρ) ^ (2 * d - 1) :=
        mul_nonneg (by linarith only [hδQ]) (pow_nonneg hA.le _)
      have hle : ((d : ℝ) - 1) * (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith [hdpos]
      have hstep2 : ((d : ℝ) - 1) * (δQ / 4 * (d : ℝ) * (uStar d - ρ) ^ (2 * d - 1))
          ≤ δQ / 4 * ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1)) := by
        rw [hfac, hfac2]
        exact mul_le_mul_of_nonneg_left hle hnn
      have hstep3 : δQ / 4 * ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1))
          ≤ δQ / 4 * ((d : ℝ) ^ 2 * w ^ (2 * d - 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hwpow (le_of_lt (pow_pos hdpos 2)))
          (by linarith only [hδQ])
      linarith only [hstep, hstep2, hstep3]
    have hdist : dist ((z, w) : ℝ × ℝ) (uStar d, uStar d) < ρ1 := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith only [hz.1, hb1], by linarith only [hz.2, hb1]⟩
      · rw [Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith only [hw.1, hb1], by linarith only [hw.2, hb1]⟩
    have hcont : |thetaV1 d (pStar d) z w - thetaV1 d (pStar d) (uStar d) (uStar d)|
        ≤ δQ / 2 / 2 := by simpa using hV1 (z, w) hdist
    have htri := abs_add_le (thetaV1 d (B.p h) z w - thetaV1 d (pStar d) z w)
      (thetaV1 d (pStar d) z w - thetaV1 d (pStar d) (uStar d) (uStar d))
    have hcollapse : thetaV1 d (B.p h) z w - thetaV1 d (pStar d) z w
        + (thetaV1 d (pStar d) z w - thetaV1 d (pStar d) (uStar d) (uStar d))
      = thetaV1 d (B.p h) z w - thetaV1 d (pStar d) (uStar d) (uStar d) := by ring
    rw [hcollapse] at htri
    linarith only [htri, hshift, hcont]
  have hV2h : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ), ∀ w ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |thetaV2 d z w - thetaV2 d (uStar d) (uStar d)| ≤ δQ / 2 := by
    intro z hz w hw
    have hdist : dist ((z, w) : ℝ × ℝ) (uStar d, uStar d) < ρ2 := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith only [hz.1, hb2], by linarith only [hz.2, hb2]⟩
      · rw [Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith only [hw.1, hb2], by linarith only [hw.2, hb2]⟩
    simpa using hV2 (z, w) hdist
  -- the two inner sandwiches, as deviation bounds
  have hΦ1 : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |B.thetaSlice1 h y z - thetaV1 d (pStar d) (uStar d) (uStar d) / 2| ≤ δQ / 4 := by
    intro z hz
    obtain ⟨hlow, hhigh⟩ := thetaSlice1_mem hd B hhh hh0 hA hBbsq hs ht hy' hz
      (m := thetaV1 d (pStar d) (uStar d) (uStar d) - δQ / 2)
      (M := thetaV1 d (pStar d) (uStar d) (uStar d) + δQ / 2)
      (fun w hw => by
        have h1 := hV1h z hz w hw
        have h2 := neg_abs_le (thetaV1 d (B.p h) z w
          - thetaV1 d (pStar d) (uStar d) (uStar d))
        linarith only [h1, h2])
      (fun w hw => by
        have h1 := hV1h z hz w hw
        have h2 := le_abs_self (thetaV1 d (B.p h) z w
          - thetaV1 d (pStar d) (uStar d) (uStar d))
        linarith only [h1, h2])
    have hres := abs_sub_half_le hlow hhigh
    linarith only [hres]
  have hΦ2 : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |B.thetaSlice2 h y z - thetaV2 d (uStar d) (uStar d) / 2| ≤ δQ / 4 := by
    intro z hz
    obtain ⟨hlow, hhigh⟩ := thetaSlice2_mem hd B hh0 hA hBbsq hs ht hy' hz
      (m := thetaV2 d (uStar d) (uStar d) - δQ / 2)
      (M := thetaV2 d (uStar d) (uStar d) + δQ / 2)
      (fun w hw => by
        have h1 := hV2h z hz w hw
        have h2 := neg_abs_le (thetaV2 d z w - thetaV2 d (uStar d) (uStar d))
        linarith only [h1, h2])
      (fun w hw => by
        have h1 := hV2h z hz w hw
        have h2 := le_abs_self (thetaV2 d z w - thetaV2 d (uStar d) (uStar d))
        linarith only [h1, h2])
    have hres := abs_sub_half_le hlow hhigh
    linarith only [hres]
  -- the outer chart second derivative
  have hQz : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |powDeriv2 d (B.thetaSlice1 h y) (B.thetaSlice2 h y) z
        - outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
            (thetaV2 d (uStar d) (uStar d) / 2)| ≤ δR / 2 := by
    intro z hz
    have hdist : dist ((z, B.thetaSlice1 h y z, B.thetaSlice2 h y z) : ℝ × ℝ × ℝ)
        (uStar d, thetaV1 d (pStar d) (uStar d) (uStar d) / 2,
          thetaV2 d (uStar d) (uStar d) / 2) < δQ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith only [hz.1, hb4], by linarith only [hz.2, hb4]⟩
      · rw [Prod.dist_eq]
        refine max_lt ?_ ?_
        · rw [Real.dist_eq]
          have hb := hΦ1 z hz
          linarith only [hb, hδQ]
        · rw [Real.dist_eq]
          have hb := hΦ2 z hz
          linarith only [hb, hδQ]
    rw [powDeriv2_eq_outerQ]
    simpa using hQ (z, B.thetaSlice1 h y z, B.thetaSlice2 h y z) hdist
  -- the outer sandwich
  have houter : |powDD d (B.thetaSlice h y) (B.sVal h) (B.tVal h) x
      - outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
          (thetaV2 d (uStar d) (uStar d) / 2) / 2| ≤ δR / 4 := by
    obtain ⟨hlow, hhigh⟩ := powDD_mem_of_powDeriv2_mem hd hA
      (phi := B.thetaSlice h y) (phi1 := B.thetaSlice1 h y) (phi2 := B.thetaSlice2 h y)
      (m := outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
        (thetaV2 d (uStar d) (uStar d) / 2) - δR / 2)
      (M := outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
        (thetaV2 d (uStar d) (uStar d) / 2) + δR / 2)
      (fun z hz => hasDerivAt_thetaSlice hd B hhh hh0 hA hBbsq hs ht hy' hz)
      (fun z hz => hasDerivAt_thetaSlice1 hd B hhh hh0 hA hBbsq hs ht hy' hz)
      (fun z hz => by
        have h1 := hQz z hz
        have h2 := neg_abs_le (powDeriv2 d (B.thetaSlice1 h y) (B.thetaSlice2 h y) z
          - outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
            (thetaV2 d (uStar d) (uStar d) / 2))
        linarith only [h1, h2])
      (fun z hz => by
        have h1 := hQz z hz
        have h2 := le_abs_self (powDeriv2 d (B.thetaSlice1 h y) (B.thetaSlice2 h y) z
          - outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
            (thetaV2 d (uStar d) (uStar d) / 2))
        linarith only [h1, h2])
      hs ht hst hx'
    have hres := abs_sub_half_le hlow hhigh
    linarith only [hres]
  -- the geometric cofactor
  have hmf : ∀ v ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |mfac d (B.sVal h) (B.tVal h) v - (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2)| ≤ δR / 2 := by
    intro v hv
    obtain ⟨hlow, hhigh⟩ := mfac_mem_Icc (d := d) hA hv hs ht
    have hl := hMf (uStar d - ρ) (by
      rw [Real.dist_eq, show uStar d - ρ - uStar d = -ρ from by ring, abs_neg,
        abs_of_pos hρpos]
      exact hb3)
    have hup := hMf (uStar d + ρ) (by
      rw [Real.dist_eq, show uStar d + ρ - uStar d = ρ from by ring, abs_of_pos hρpos]
      exact hb3)
    rw [abs_le] at hl hup ⊢
    constructor
    · linarith only [hlow, hl.1, hl.2]
    · linarith only [hhigh, hup.1, hup.2]
  -- the assembly
  have hdistR : dist ((mfac d (B.sVal h) (B.tVal h) x, mfac d (B.sVal h) (B.tVal h) y,
      powDD d (B.thetaSlice h y) (B.sVal h) (B.tVal h) x) : ℝ × ℝ × ℝ)
      ((d : ℝ) ^ 2 * uStar d ^ (2 * d - 2), (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2),
        outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
          (thetaV2 d (uStar d) (uStar d) / 2) / 2) < δR := by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq]
      have hb := hmf x hx'
      linarith only [hb, hδR]
    · rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq]
        have hb := hmf y hy'
        linarith only [hb, hδR]
      · rw [Real.dist_eq]
        linarith only [houter, hδR]
  have hfin : |mfac d (B.sVal h) (B.tVal h) x * mfac d (B.sVal h) (B.tVal h) y
      * powDD d (B.thetaSlice h y) (B.sVal h) (B.tVal h) x
      - (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) * ((d : ℝ) ^ 2 * uStar d ^ (2 * d - 2))
        * (outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
            (thetaV2 d (uStar d) (uStar d) / 2) / 2)| ≤ ε := by
    simpa using hR _ hdistR
  have hval : (d : ℝ) ^ 2 * uStar d ^ (2 * d - 2) * ((d : ℝ) ^ 2 * uStar d ^ (2 * d - 2))
      * (outerQ d (uStar d) (thetaV1 d (pStar d) (uStar d) (uStar d) / 2)
          (thetaV2 d (uStar d) (uStar d) / 2) / 2) = (d : ℝ) ^ 3 / 4 := by
    have hcv := thetaV_theta_value (d := d) hd
    rw [outerQ, ← hcv]
    ring
  rw [kernelTheta_eq, ← hval]
  exact hfin

/-! ## The remaining coefficient bounds: the one-variable functions `u_{0,h}`, `u_{d,h}`

The proof of `lem:central-kernel-bound` bounds all coefficients and one-variable functions by a
single constant, `max{|p_{ij,h}|, |u_{i,h}(x)|, |v_{i,h}(y)|} ≤ C_d` for `x,y ∈ 𝒩_{ρ_0}`; here
the bounds are proved on a closed window of prescribed radius.
`SingularEndpoint/AuxiliaryLagrangian/PowFirstOrder.lean` proved them for the four coefficients of
`P_h`; what was left were `u_{0,h}`, `u_{d,h}` — equal to `v_{0,h}`, `v_{d,h}` by symmetry of
the kernel — and, as a Lean convenience not listed in that bound, `Θ_h`.  Each is `mfac`,
bounded by `mfac_mem_Icc`, times a **second** divided
difference of a coefficient slice, so all that is needed beyond `SingularEndpoint/AuxiliaryLagrangian/PowFirstOrder.lean`
is one more differentiation of `A_h` and `B_h`: that is `hasDerivAt_kernelCoefA_fst` and
`hasDerivAt_kernelCoefB_fst`, whose values are the coefficients of `kSlice2`. -/

/-- **The second derivative of the constant coefficient slice.**  `A_h'` is the *fixed* linear
functional `powCoefA · s_h t_h` of the differentiated slice `kSlice1`, so `A_h''` is the same
functional of `kSlice2 = ∂_z kSlice1`. -/
theorem hasDerivAt_kernelCoefA_fst (B : KKTFamily d) {h x : ℝ} (hp0 : 0 < B.p h)
    (hp1 : B.p h < 1) (hs0 : 0 < x * B.sVal h) (hs1 : x * B.sVal h < 1)
    (ht0 : 0 < x * B.tVal h) (ht1 : x * B.tVal h < 1) :
    HasDerivAt (fun ζ => powCoefA d (kSlice1 (B.p h) ζ) (B.sVal h) (B.tVal h))
      (powCoefA d (kSlice2 x) (B.sVal h) (B.tVal h)) x := by
  have hS := hasDerivAt_kSlice1_fst (p := B.p h) (z := x) (w := B.sVal h) hp0 hp1 hs0 hs1
  have hT := hasDerivAt_kSlice1_fst (p := B.p h) (z := x) (w := B.tVal h) hp0 hp1 ht0 ht1
  exact hS.sub (((hT.sub hS).div_const (B.tVal h ^ d - B.sVal h ^ d)).mul_const (B.sVal h ^ d))

/-- **The second derivative of the `y^d` coefficient slice**, the companion of
`hasDerivAt_kernelCoefA_fst`. -/
theorem hasDerivAt_kernelCoefB_fst (B : KKTFamily d) {h x : ℝ} (hp0 : 0 < B.p h)
    (hp1 : B.p h < 1) (hs0 : 0 < x * B.sVal h) (hs1 : x * B.sVal h < 1)
    (ht0 : 0 < x * B.tVal h) (ht1 : x * B.tVal h < 1) :
    HasDerivAt (fun ζ => powCoefB d (kSlice1 (B.p h) ζ) (B.sVal h) (B.tVal h))
      (powCoefB d (kSlice2 x) (B.sVal h) (B.tVal h)) x := by
  have hS := hasDerivAt_kSlice1_fst (p := B.p h) (z := x) (w := B.sVal h) hp0 hp1 hs0 hs1
  have hT := hasDerivAt_kSlice1_fst (p := B.p h) (z := x) (w := B.tVal h) hp0 hp1 ht0 ht1
  exact (hT.sub hS).div_const (B.tVal h ^ d - B.sVal h ^ d)

/-- The four coefficients of the two differentiated slices are bounded on the central window,
uniformly in small `h`: `abs_powCoefB_le_of_abs_powDeriv_le` and `abs_powCoefA_le`
(`SingularEndpoint/AuxiliaryLagrangian/PowFirstOrder.lean`) fed with the entropy bounds `exists_abs_Jp'_le`,
`abs_Jp''_le`, `abs_Jp3_le`. -/
private theorem exists_coef_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      |h| < B.h₀ ∧ B.sVal h ∈ centralWindow d ρ ∧ B.tVal h ∈ centralWindow d ρ ∧
        ∀ x ∈ centralWindow d ρ,
          |powCoefA d (kSlice1 (B.p h) x) (B.sVal h) (B.tVal h)| ≤ C ∧
          |powCoefB d (kSlice1 (B.p h) x) (B.sVal h) (B.tVal h)| ≤ C ∧
          |powCoefA d (kSlice2 x) (B.sVal h) (B.tVal h)| ≤ C ∧
          |powCoefB d (kSlice2 x) (B.sVal h) (B.tVal h)| ≤ C := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hd0 : d ≠ 0 := by omega
  have hA : 0 < uStar d - ρ := by linarith
  have hB1 : uStar d + ρ < 1 := by linarith
  have hB0 : (0 : ℝ) < uStar d + ρ := by linarith
  have hmm : 0 < (uStar d - ρ) * (uStar d - ρ) := mul_pos hA hA
  have hMM : (uStar d + ρ) * (uStar d + ρ) < 1 := by nlinarith
  obtain ⟨C₁, hC₁, δ₁, hδ₁, hJ1⟩ := exists_abs_Jp'_le hd B hmm hMM
  obtain ⟨δ₂, hδ₂, hatoms⟩ := exists_atoms_mem_centralWindow B hρ
  obtain ⟨CJ, hCJ0, hCJa, hCJb, hCJc⟩ :
      ∃ CJ : ℝ, 0 < CJ ∧ C₁ ≤ CJ ∧
        1 / ((uStar d - ρ) * (uStar d - ρ) * (1 - (uStar d + ρ) * (uStar d + ρ))) ≤ CJ ∧
        (1 / ((uStar d - ρ) * (uStar d - ρ)) ^ 2
          + 1 / (1 - (uStar d + ρ) * (uStar d + ρ)) ^ 2) ≤ CJ := by
    refine ⟨C₁ + |1 / ((uStar d - ρ) * (uStar d - ρ) * (1 - (uStar d + ρ) * (uStar d + ρ)))|
        + |1 / ((uStar d - ρ) * (uStar d - ρ)) ^ 2
          + 1 / (1 - (uStar d + ρ) * (uStar d + ρ)) ^ 2|, ?_, ?_, ?_, ?_⟩
    · have h1 := abs_nonneg (1 / ((uStar d - ρ) * (uStar d - ρ)
        * (1 - (uStar d + ρ) * (uStar d + ρ))))
      have h2 := abs_nonneg (1 / ((uStar d - ρ) * (uStar d - ρ)) ^ 2
        + 1 / (1 - (uStar d + ρ) * (uStar d + ρ)) ^ 2)
      linarith
    · have h1 := abs_nonneg (1 / ((uStar d - ρ) * (uStar d - ρ)
        * (1 - (uStar d + ρ) * (uStar d + ρ))))
      have h2 := abs_nonneg (1 / ((uStar d - ρ) * (uStar d - ρ)) ^ 2
        + 1 / (1 - (uStar d + ρ) * (uStar d + ρ)) ^ 2)
      linarith
    · have h1 := le_abs_self (1 / ((uStar d - ρ) * (uStar d - ρ)
        * (1 - (uStar d + ρ) * (uStar d + ρ))))
      have h2 := abs_nonneg (1 / ((uStar d - ρ) * (uStar d - ρ)) ^ 2
        + 1 / (1 - (uStar d + ρ) * (uStar d + ρ)) ^ 2)
      linarith
    · have h1 := abs_nonneg (1 / ((uStar d - ρ) * (uStar d - ρ)
        * (1 - (uStar d + ρ) * (uStar d + ρ))))
      have h2 := le_abs_self (1 / ((uStar d - ρ) * (uStar d - ρ)) ^ 2
        + 1 / (1 - (uStar d + ρ) * (uStar d + ρ)) ^ 2)
      linarith
  refine ⟨1 + |(uStar d + ρ) * CJ| + |(CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * (1 + |(uStar d + ρ) ^ d|)
    + |(uStar d + ρ) * (uStar d + ρ) * CJ|
    + |(2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * (1 + |(uStar d + ρ) ^ d|), by positivity,
    min (min δ₁ δ₂) B.h₀, lt_min (lt_min hδ₁ hδ₂) B.h₀_pos, ?_⟩
  intro h hh0 hhδ
  have habs : |h| = h := abs_of_pos hh0
  have hdb : |h| < B.h₀ := by
    rw [habs]
    exact lt_of_lt_of_le hhδ (min_le_right _ _)
  have hdd1 : |h| < δ₁ := by
    rw [habs]
    exact lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hdd2 : h < δ₂ := lt_of_lt_of_le hhδ (le_trans (min_le_left _ _) (min_le_right _ _))
  obtain ⟨hsmem, htmem⟩ := hatoms h hh0 hdd2
  refine ⟨hdb, hsmem, htmem, ?_⟩
  have hp := B.p_mem h hdb
  have hs : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hsmem
  have ht : B.tVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := htmem
  have hs0 : 0 < B.sVal h := lt_of_lt_of_le hA hs.1
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  have hJ : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      ∀ w ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      (0 < z * w ∧ z * w < 1) ∧ |Jp' (B.p h) (z * w)| ≤ CJ ∧ |Jp'' (z * w)| ≤ CJ ∧
        |Jp3 (z * w)| ≤ CJ := by
    intro z hz w hw
    have hz0 : 0 < z := lt_of_lt_of_le hA hz.1
    have hw0 : 0 < w := lt_of_lt_of_le hA hw.1
    have hlow : (uStar d - ρ) * (uStar d - ρ) ≤ z * w := mul_le_mul hz.1 hw.1 hA.le hz0.le
    have hhigh : z * w ≤ (uStar d + ρ) * (uStar d + ρ) := mul_le_mul hz.2 hw.2 hw0.le hB0.le
    have hmem : z * w ∈ Set.Icc ((uStar d - ρ) * (uStar d - ρ)) ((uStar d + ρ) * (uStar d + ρ)) :=
      ⟨hlow, hhigh⟩
    exact ⟨⟨mul_pos hz0 hw0, lt_of_le_of_lt hhigh hMM⟩,
      le_trans (hJ1 h hdd1 (z * w) hmem) hCJa,
      le_trans (abs_Jp''_le hmm hMM hmem) hCJb, le_trans (abs_Jp3_le hmm hMM hmem) hCJc⟩
  intro x hx
  have hx' : x ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hx
  have hx0 : 0 < x := lt_of_lt_of_le hA hx'.1
  -- the first differentiated slice
  have hd1s : ∀ w ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      HasDerivAt (kSlice1 (B.p h) x) (kSlice1w (B.p h) x w) w := fun w hw =>
    hasDerivAt_kSlice1_snd hp.1 hp.2 (hJ x hx' w hw).1.1 (hJ x hx' w hw).1.2
  have hb1 : ∀ w ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |powDeriv d (kSlice1w (B.p h) x) w|
        ≤ (CJ + (uStar d + ρ) * (uStar d + ρ) * CJ) / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) := by
    intro w hw
    refine abs_powDeriv_le hd0 hA hw ?_
    obtain ⟨-, hJa, hJb, -⟩ := hJ x hx' w hw
    have hw0 : 0 < w := lt_of_lt_of_le hA hw.1
    have htri := abs_add_le (Jp' (B.p h) (x * w)) (w * x * Jp'' (x * w))
    have hprod : |w * x * Jp'' (x * w)| ≤ (uStar d + ρ) * (uStar d + ρ) * CJ := by
      rw [abs_mul, abs_mul, abs_of_pos hw0, abs_of_pos hx0]
      have hle : w * x ≤ (uStar d + ρ) * (uStar d + ρ) := mul_le_mul hw.2 hx'.2 hx0.le hB0.le
      exact mul_le_mul hle hJb (abs_nonneg _) (mul_nonneg hB0.le hB0.le)
    have hgoal : |kSlice1w (B.p h) x w| ≤ CJ + (uStar d + ρ) * (uStar d + ρ) * CJ := by
      simp only [kSlice1w]
      linarith
    exact hgoal
  have hB1c : |powCoefB d (kSlice1 (B.p h) x) (B.sVal h) (B.tVal h)|
      ≤ (CJ + (uStar d + ρ) * (uStar d + ρ) * CJ) / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) :=
    abs_powCoefB_le_of_abs_powDeriv_le hd0 hA hd1s hb1 hs ht hst
  have hK1 : (0 : ℝ) ≤ (CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) := le_trans (abs_nonneg _) hB1c
  have hnode1 : |kSlice1 (B.p h) x (B.sVal h)| ≤ (uStar d + ρ) * CJ := by
    obtain ⟨-, hJa, -, -⟩ := hJ x hx' (B.sVal h) hs
    simp only [kSlice1]
    rw [abs_mul, abs_of_pos hs0]
    exact mul_le_mul hs.2 hJa (abs_nonneg _) hB0.le
  have hpowle : B.sVal h ^ d ≤ (uStar d + ρ) ^ d := pow_le_pow_left₀ hs0.le hs.2 d
  have hA1c : |powCoefA d (kSlice1 (B.p h) x) (B.sVal h) (B.tVal h)|
      ≤ (uStar d + ρ) * CJ
        + (CJ + (uStar d + ρ) * (uStar d + ρ) * CJ) / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))
          * (uStar d + ρ) ^ d := by
    have hkey := abs_powCoefA_le (d := d) (phi := kSlice1 (B.p h) x) hs0.le hnode1 hB1c
    have hmulle := mul_le_mul_of_nonneg_left hpowle hK1
    linarith
  -- the second differentiated slice
  have hd2s : ∀ w ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      HasDerivAt (kSlice2 x) (kSlice2w x w) w := fun w hw =>
    hasDerivAt_kSlice2_snd (hJ x hx' w hw).1.1 (hJ x hx' w hw).1.2
  have hb2 : ∀ w ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |powDeriv d (kSlice2w x) w|
        ≤ (2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
            / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) := by
    intro w hw
    refine abs_powDeriv_le hd0 hA hw ?_
    obtain ⟨-, -, hJb, hJc⟩ := hJ x hx' w hw
    have hw0 : 0 < w := lt_of_lt_of_le hA hw.1
    have htri := abs_add_le (2 * w * Jp'' (x * w)) (w ^ 2 * x * Jp3 (x * w))
    have hsq : w ^ 2 ≤ (uStar d + ρ) * (uStar d + ρ) := by
      rw [sq]
      exact mul_le_mul hw.2 hw.2 hw0.le hB0.le
    have hp1' : |2 * w * Jp'' (x * w)| ≤ 2 * (uStar d + ρ) * CJ := by
      rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_pos hw0]
      have hle : 2 * w ≤ 2 * (uStar d + ρ) := by linarith [hw.2]
      have hres := mul_le_mul hle hJb (abs_nonneg _) (by linarith)
      linarith [hres]
    have hp2' : |w ^ 2 * x * Jp3 (x * w)|
        ≤ (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ := by
      rw [abs_mul, abs_mul, abs_of_pos (pow_pos hw0 2), abs_of_pos hx0]
      have hle : w ^ 2 * x ≤ (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) :=
        mul_le_mul hsq hx'.2 hx0.le (mul_nonneg hB0.le hB0.le)
      exact mul_le_mul hle hJc (abs_nonneg _) (mul_nonneg (mul_nonneg hB0.le hB0.le) hB0.le)
    have hgoal : |kSlice2w x w|
        ≤ 2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ := by
      simp only [kSlice2w]
      linarith
    exact hgoal
  have hB2c : |powCoefB d (kSlice2 x) (B.sVal h) (B.tVal h)|
      ≤ (2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
          / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) :=
    abs_powCoefB_le_of_abs_powDeriv_le hd0 hA hd2s hb2 hs ht hst
  have hK2 : (0 : ℝ) ≤ (2 * (uStar d + ρ) * CJ
      + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) := le_trans (abs_nonneg _) hB2c
  have hnode2 : |kSlice2 x (B.sVal h)| ≤ (uStar d + ρ) * (uStar d + ρ) * CJ := by
    obtain ⟨-, -, hJb, -⟩ := hJ x hx' (B.sVal h) hs
    simp only [kSlice2]
    rw [abs_mul, abs_of_pos (pow_pos hs0 2)]
    have hle : B.sVal h ^ 2 ≤ (uStar d + ρ) * (uStar d + ρ) := by
      rw [sq]
      exact mul_le_mul hs.2 hs.2 hs0.le hB0.le
    exact mul_le_mul hle hJb (abs_nonneg _) (mul_nonneg hB0.le hB0.le)
  have hA2c : |powCoefA d (kSlice2 x) (B.sVal h) (B.tVal h)|
      ≤ (uStar d + ρ) * (uStar d + ρ) * CJ
        + (2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
            / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d := by
    have hkey := abs_powCoefA_le (d := d) (phi := kSlice2 x) hs0.le hnode2 hB2c
    have hmulle := mul_le_mul_of_nonneg_left hpowle hK2
    linarith
  -- everything is under the single constant
  have e1 := le_abs_self ((uStar d + ρ) * CJ)
  have e2 := le_abs_self ((CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
    / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)))
  have e3 := le_abs_self ((uStar d + ρ) * (uStar d + ρ) * CJ)
  have e4 := le_abs_self ((2 * (uStar d + ρ) * CJ
    + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
    / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)))
  have f1 := abs_nonneg ((uStar d + ρ) * CJ)
  have f2 := abs_nonneg ((CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
    / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)))
  have f3 := abs_nonneg ((uStar d + ρ) * (uStar d + ρ) * CJ)
  have f4 := abs_nonneg ((2 * (uStar d + ρ) * CJ
    + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
    / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)))
  have g1 := le_abs_self ((uStar d + ρ) ^ d)
  have g2 := abs_nonneg ((uStar d + ρ) ^ d)
  have hmul1 : (CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d
      ≤ |(CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * (1 + |(uStar d + ρ) ^ d|) := by
    have hstep : (CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d
        ≤ |(CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
          / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * |(uStar d + ρ) ^ d| := by
      have := abs_mul ((CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))) ((uStar d + ρ) ^ d)
      have hle := le_abs_self ((CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d)
      linarith only [this, hle]
    exact le_trans hstep
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) f2)
  have hmul2 : (2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d
      ≤ |(2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * (1 + |(uStar d + ρ) ^ d|) := by
    have hstep : (2 * (uStar d + ρ) * CJ
          + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d
        ≤ |(2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
          / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * |(uStar d + ρ) ^ d| := by
      have := abs_mul ((2 * (uStar d + ρ) * CJ
        + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))) ((uStar d + ρ) ^ d)
      have hle := le_abs_self ((2 * (uStar d + ρ) * CJ
        + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1)) * (uStar d + ρ) ^ d)
      linarith only [this, hle]
    exact le_trans hstep
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) f4)
  have f2' : (0 : ℝ) ≤ |(CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * (1 + |(uStar d + ρ) ^ d|) :=
    mul_nonneg f2 (by linarith only [g2])
  have f4' : (0 : ℝ) ≤ |(2 * (uStar d + ρ) * CJ
      + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * (1 + |(uStar d + ρ) ^ d|) :=
    mul_nonneg f4 (by linarith only [g2])
  have f2'' : |(CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))|
      ≤ |(CJ + (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * (1 + |(uStar d + ρ) ^ d|) :=
    le_mul_of_one_le_right f2 (by linarith only [g2])
  have f4'' : |(2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
      / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))|
      ≤ |(2 * (uStar d + ρ) * CJ + (uStar d + ρ) * (uStar d + ρ) * (uStar d + ρ) * CJ)
        / ((d : ℝ) * (uStar d - ρ) ^ (d - 1))| * (1 + |(uStar d + ρ) ^ d|) :=
    le_mul_of_one_le_right f4 (by linarith only [g2])
  exact ⟨by linarith only [hA1c, e1, hmul1, f3, f4'],
    by linarith only [hB1c, e2, f2'', f1, f3, f4'],
    by linarith only [hA2c, e3, hmul2, f1, f2'],
    by linarith only [hB2c, e4, f4'', f1, f2', f3]⟩

/-- **`u_{0,h}` is bounded on the central window, uniformly in small `h`** — the
coefficient-bound clause of the proof of `lem:central-kernel-bound` for the first one-variable
function.  `u_{0,h}` is `mfac`
(bounded by `mfac_mem_Icc`) times the second divided difference of the coefficient slice
`A_h`, and `powDD_mem_of_powDeriv2_mem` bounds that through the chain `A_h → A_h' → A_h''`
supplied by `hasDerivAt_kernelCoefA` and `hasDerivAt_kernelCoefA_fst`. -/
theorem exists_u0_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ x ∈ centralWindow d ρ, |B.u0 h x| ≤ C := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hone : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hA : 0 < uStar d - ρ := by linarith
  have hB0 : (0 : ℝ) < uStar d + ρ := by linarith
  have hB1 : uStar d + ρ < 1 := by linarith
  obtain ⟨C, hC, δ, hδ, hdata⟩ := exists_coef_window hd B hρ hρu hρ1
  have hnum : (0 : ℝ) < (uStar d + ρ) * C + ((d : ℝ) - 1) * C := by
    have h1 : (0 : ℝ) < (uStar d + ρ) * C := mul_pos hB0 hC
    have h2 : (0 : ℝ) ≤ ((d : ℝ) - 1) * C := mul_nonneg (by linarith) hC.le
    linarith
  have hden : (0 : ℝ) < (d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1) :=
    mul_pos (pow_pos (dpos hd) 2) (pow_pos hA _)
  have hfac : (0 : ℝ) < (d : ℝ) ^ 2 * (uStar d + ρ) ^ (2 * d - 2) :=
    mul_pos (pow_pos (dpos hd) 2) (pow_pos hB0 _)
  refine ⟨(d : ℝ) ^ 2 * (uStar d + ρ) ^ (2 * d - 2)
    * (((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
      / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1)) / 2),
    mul_pos hfac (div_pos (div_pos hnum hden) two_pos), δ, hδ, ?_⟩
  intro h hh0 hhδ x hx
  obtain ⟨hdb, hsmem, htmem, hcoef⟩ := hdata h hh0 hhδ
  have hp := B.p_mem h hdb
  have hs : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hsmem
  have ht : B.tVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := htmem
  have hx' : x ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hx
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  have hmul : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      ∀ w ∈ Set.Icc (uStar d - ρ) (uStar d + ρ), 0 < z * w ∧ z * w < 1 := by
    intro z hz w hw
    have hz0 : 0 < z := lt_of_lt_of_le hA hz.1
    have hw0 : 0 < w := lt_of_lt_of_le hA hw.1
    refine ⟨mul_pos hz0 hw0, ?_⟩
    have hhigh : z * w ≤ (uStar d + ρ) * (uStar d + ρ) := mul_le_mul hz.2 hw.2 hw0.le hB0.le
    nlinarith [hhigh, hB0, hB1]
  have hchain : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      HasDerivAt (B.kernelCoefA h)
        (powCoefA d (kSlice1 (B.p h) z) (B.sVal h) (B.tVal h)) z := fun z hz =>
    hasDerivAt_kernelCoefA B hp.1 hp.2 (hmul z hz _ hs).1 (hmul z hz _ hs).2
      (hmul z hz _ ht).1 (hmul z hz _ ht).2
  have hchain2 : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      HasDerivAt (fun ζ => powCoefA d (kSlice1 (B.p h) ζ) (B.sVal h) (B.tVal h))
        (powCoefA d (kSlice2 z) (B.sVal h) (B.tVal h)) z := fun z hz =>
    hasDerivAt_kernelCoefA_fst B hp.1 hp.2 (hmul z hz _ hs).1 (hmul z hz _ hs).2
      (hmul z hz _ ht).1 (hmul z hz _ ht).2
  have hK : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |powDeriv2 d (fun ζ => powCoefA d (kSlice1 (B.p h) ζ) (B.sVal h) (B.tVal h))
        (fun ζ => powCoefA d (kSlice2 ζ) (B.sVal h) (B.tVal h)) z|
        ≤ ((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
            / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1)) := by
    intro z hz
    obtain ⟨hAA, -, hBB, -⟩ := hcoef z hz
    exact abs_powDeriv2_le hd hA hz hAA hBB
  obtain ⟨hlow, hhigh⟩ := powDD_mem_of_powDeriv2_mem hd hA
    (phi := B.kernelCoefA h)
    (phi1 := fun ζ => powCoefA d (kSlice1 (B.p h) ζ) (B.sVal h) (B.tVal h))
    (phi2 := fun ζ => powCoefA d (kSlice2 ζ) (B.sVal h) (B.tVal h))
    (m := -(((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
      / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1))))
    (M := ((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
      / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1)))
    hchain hchain2 (fun z hz => (abs_le.mp (hK z hz)).1) (fun z hz => (abs_le.mp (hK z hz)).2)
    hs ht hst hx'
  have habsq : |powDD d (B.kernelCoefA h) (B.sVal h) (B.tVal h) x|
      ≤ ((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
          / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1)) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hmlow, hmhigh⟩ := mfac_mem_Icc (d := d) hA hx' hs ht
  have hmnn : (0 : ℝ) ≤ mfac d (B.sVal h) (B.tVal h) x := by
    have hq : (0 : ℝ) ≤ (d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 2) :=
      (mul_pos (pow_pos (dpos hd) 2) (pow_pos hA _)).le
    linarith
  rw [u0, abs_mul, abs_of_nonneg hmnn]
  exact mul_le_mul hmhigh habsq (abs_nonneg _) hfac.le

/-- **`u_{d,h}` is bounded on the central window, uniformly in small `h`** — the same statement
for the second one-variable function, through the chain `B_h → B_h' → B_h''`.  By symmetry of
the kernel these two bounds are also the bounds on `v_{0,h}`, `v_{d,h}`. -/
theorem exists_ud_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) (hρ1 : ρ ≤ (1 - uStar d) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ x ∈ centralWindow d ρ, |B.ud h x| ≤ C := by
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hone : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hA : 0 < uStar d - ρ := by linarith
  have hB0 : (0 : ℝ) < uStar d + ρ := by linarith
  have hB1 : uStar d + ρ < 1 := by linarith
  obtain ⟨C, hC, δ, hδ, hdata⟩ := exists_coef_window hd B hρ hρu hρ1
  have hnum : (0 : ℝ) < (uStar d + ρ) * C + ((d : ℝ) - 1) * C := by
    have h1 : (0 : ℝ) < (uStar d + ρ) * C := mul_pos hB0 hC
    have h2 : (0 : ℝ) ≤ ((d : ℝ) - 1) * C := mul_nonneg (by linarith) hC.le
    linarith
  have hden : (0 : ℝ) < (d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1) :=
    mul_pos (pow_pos (dpos hd) 2) (pow_pos hA _)
  have hfac : (0 : ℝ) < (d : ℝ) ^ 2 * (uStar d + ρ) ^ (2 * d - 2) :=
    mul_pos (pow_pos (dpos hd) 2) (pow_pos hB0 _)
  refine ⟨(d : ℝ) ^ 2 * (uStar d + ρ) ^ (2 * d - 2)
    * (((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
      / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1)) / 2),
    mul_pos hfac (div_pos (div_pos hnum hden) two_pos), δ, hδ, ?_⟩
  intro h hh0 hhδ x hx
  obtain ⟨hdb, hsmem, htmem, hcoef⟩ := hdata h hh0 hhδ
  have hp := B.p_mem h hdb
  have hs : B.sVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hsmem
  have ht : B.tVal h ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := htmem
  have hx' : x ∈ Set.Icc (uStar d - ρ) (uStar d + ρ) := hx
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hh0
  have hmul : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      ∀ w ∈ Set.Icc (uStar d - ρ) (uStar d + ρ), 0 < z * w ∧ z * w < 1 := by
    intro z hz w hw
    have hz0 : 0 < z := lt_of_lt_of_le hA hz.1
    have hw0 : 0 < w := lt_of_lt_of_le hA hw.1
    refine ⟨mul_pos hz0 hw0, ?_⟩
    have hhigh : z * w ≤ (uStar d + ρ) * (uStar d + ρ) := mul_le_mul hz.2 hw.2 hw0.le hB0.le
    nlinarith [hhigh, hB0, hB1]
  have hchain : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      HasDerivAt (B.kernelCoefB h)
        (powCoefB d (kSlice1 (B.p h) z) (B.sVal h) (B.tVal h)) z := fun z hz =>
    hasDerivAt_kernelCoefB B hp.1 hp.2 (hmul z hz _ hs).1 (hmul z hz _ hs).2
      (hmul z hz _ ht).1 (hmul z hz _ ht).2
  have hchain2 : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      HasDerivAt (fun ζ => powCoefB d (kSlice1 (B.p h) ζ) (B.sVal h) (B.tVal h))
        (powCoefB d (kSlice2 z) (B.sVal h) (B.tVal h)) z := fun z hz =>
    hasDerivAt_kernelCoefB_fst B hp.1 hp.2 (hmul z hz _ hs).1 (hmul z hz _ hs).2
      (hmul z hz _ ht).1 (hmul z hz _ ht).2
  have hK : ∀ z ∈ Set.Icc (uStar d - ρ) (uStar d + ρ),
      |powDeriv2 d (fun ζ => powCoefB d (kSlice1 (B.p h) ζ) (B.sVal h) (B.tVal h))
        (fun ζ => powCoefB d (kSlice2 ζ) (B.sVal h) (B.tVal h)) z|
        ≤ ((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
            / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1)) := by
    intro z hz
    obtain ⟨-, hAA, -, hBB⟩ := hcoef z hz
    exact abs_powDeriv2_le hd hA hz hAA hBB
  obtain ⟨hlow, hhigh⟩ := powDD_mem_of_powDeriv2_mem hd hA
    (phi := B.kernelCoefB h)
    (phi1 := fun ζ => powCoefB d (kSlice1 (B.p h) ζ) (B.sVal h) (B.tVal h))
    (phi2 := fun ζ => powCoefB d (kSlice2 ζ) (B.sVal h) (B.tVal h))
    (m := -(((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
      / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1))))
    (M := ((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
      / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1)))
    hchain hchain2 (fun z hz => (abs_le.mp (hK z hz)).1) (fun z hz => (abs_le.mp (hK z hz)).2)
    hs ht hst hx'
  have habsq : |powDD d (B.kernelCoefB h) (B.sVal h) (B.tVal h) x|
      ≤ ((uStar d + ρ) * C + ((d : ℝ) - 1) * C)
          / ((d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 1)) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hmlow, hmhigh⟩ := mfac_mem_Icc (d := d) hA hx' hs ht
  have hmnn : (0 : ℝ) ≤ mfac d (B.sVal h) (B.tVal h) x := by
    have hq : (0 : ℝ) ≤ (d : ℝ) ^ 2 * (uStar d - ρ) ^ (2 * d - 2) :=
      (mul_pos (pow_pos (dpos hd) 2) (pow_pos hA _)).le
    linarith
  rw [ud, abs_mul, abs_of_nonneg hmnn]
  exact mul_le_mul hmhigh habsq (abs_nonneg _) hfac.le

/-- **`Θ_h` is bounded on the central square** (not part of the paper's coefficient-bound
clause, which omits `Θ_h`): an immediate
corollary of `exists_kernelTheta_error` at `ε = 1`.  As there, the window radius is produced
rather than prescribed. -/
theorem exists_kernelTheta_bound (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ hρ : ℝ, 0 < hρ ∧ ∀ h : ℝ, 0 < h → h < hρ →
      ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
        |B.kernelTheta h x y| ≤ (d : ℝ) ^ 3 / 4 + 1 := by
  obtain ⟨ρ, hρ, hρ', hρ'0, hbnd⟩ := exists_kernelTheta_error hd B 1 one_pos
  refine ⟨ρ, hρ, hρ', hρ'0, ?_⟩
  intro h hh0 hhδ x hx y hy
  have hb := hbnd h hh0 hhδ x hx y hy
  have htri := abs_add_le (B.kernelTheta h x y - (d : ℝ) ^ 3 / 4) ((d : ℝ) ^ 3 / 4)
  have hcollapse : B.kernelTheta h x y - (d : ℝ) ^ 3 / 4 + (d : ℝ) ^ 3 / 4
      = B.kernelTheta h x y := by ring
  rw [hcollapse] at htri
  have hpos : |(d : ℝ) ^ 3 / 4| = (d : ℝ) ^ 3 / 4 :=
    abs_of_pos (by positivity)
  rw [hpos] at htri
  linarith

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
