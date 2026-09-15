import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.Interp2
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs

/-!
# One-variable interpolation in the basis `{1, x^d}` (Section 5, `paper/sections/singular_auxiliary_lagrangian.tex`)

The one-variable foundation of `lem:central-kernel-bound`.  That lemma expands the law kernel
`K_h` on the central square by interpolating **in each variable separately** in the basis
`{1, x^d}` at the two nodes `s_h, t_h` — the operator `I_h^x` of
`eq:moment-interpolation` — and needs its coefficients and its remainder to stay bounded as
the nodes coalesce.  This file builds the one-variable half of that theory; the two-variable
assembly (`I_h^xI_h^y`, `lem:central-kernel-bound`) is a later file and is
**not** treated here.

## The change of variable, packaged once

The paper's own advice, in the proof of `lem:central-kernel-bound`, is to work in
the analytic coordinate `w = x^d` near
`u_* > 0`: there `eq:moment-interpolation` is *ordinary linear interpolation* at the nodes
`s_h^d, t_h^d`, so the arity-2 theory of `SingularEndpoint/AuxiliaryLagrangian/Interp2.lean` applies verbatim.  The whole
point of this file is to perform that substitution once and for all, so that later work never
touches it again:

* `powChart d φ w = φ (w ^ (1/d))` reads a function of `x` as a function of `w`, and
  `powChart_pow` is the round trip `powChart d φ (x^d) = φ x` for `x ≥ 0`;
* `powDD` is `Interp2`'s total second divided difference `dd2` of `powChart d φ` at the nodes
  `s^d, t^d`, evaluated at `x^d`;
* `powDeriv`, `powDeriv2` are the first and second derivatives **with respect to `w`**,
  written as explicit expressions in `x` , and `hasDerivAt_powChart` is the chain
  rule that identifies them with the honest `w`-derivatives of `powChart`.

Everything is stated for `x > 0`, where `x ↦ x^d` is a strictly monotone real-analytic
bijection onto `w > 0`; the inverse is `Real.rpow` with exponent `(d : ℝ)⁻¹`, exactly as in
`KKTFamily.rVal` (`SingularEndpoint/RankOneStationaryFamily/Family.lean`).

## The coalescing operator `𝒟_d`

The operator
`𝒟_d F = ½ (F''(u_*) - (d-1)/u_* · F'(u_*))` is the value at the coalescing limit of
`R_0^xF(x)/(x - u_*)^2`.  The paper does not name it: the proof of `lem:central-kernel-bound`
works with `½∂_w²` in the coordinate `w = x^d` instead.  It is `powDop` below, and
`powDop_eq_powDeriv2` is the correspondence

  `powDop d φ₁ φ₂ x = (d² x^{2d-2} / 2) · powDeriv2 d φ₁ φ₂ x`,

which is the `(x - u_*)^2` versus `(x^d - u_*^d)^2` normalisation: the remainder of this file
is a multiple of `(x^d - s^d)(x^d - t^d)`, and `(x^d - u_*^d)^2 / (x - u_*)^2 → d² u_*^{2d-2}`.
The constant `Θ_0(u_*,u_*) = d^3/4` quoted in the proof of
`lem:central-kernel-bound` can therefore be checked later from
`powDop_eq_powDeriv2` alone, without revisiting the change of variable.

## Relation to `SingularEndpoint/AuxiliaryLagrangian/TailScalar.lean`

`TailScalar.lean` already carries these definitions for the single function
`φ(u) = J̃_{p_h}(x̃u)` of the closed-window route to `lem:auxiliary-lagrangian-bound`
(`exists_tail_interpolation`); that file is the special case

  `B.gCoefB h xt = powCoefB d (fun u => B.JpTildeH h (xt * u)) (B.sVal h) (B.tVal h)`,
  `B.gCoefA h xt = powCoefA d (fun u => B.JpTildeH h (xt * u)) (B.sVal h) (B.tVal h)`,
  `B.gfun   h xt = powResid d (fun u => B.JpTildeH h (xt * u)) (B.sVal h) (B.tVal h)`,

all three by `rfl`, and `gfun_sVal`, `gfun_tVal` are `powResid_left`, `powResid_right`.
`TailScalar.lean` is left untouched: it needs no derivative of `φ` (the continued entropy is
only Lipschitz-up-to-a-log there), whereas everything below the definitions here is a
mean-value argument and does need one.

## Contents

* `powCoefB`, `powCoefA`, `powResid` — the interpolant of `φ` in `{1, x^d}` at nodes `s, t`
  and its residual, with `powResid_left`, `powResid_right`;
* `powChart`, `powChart_pow` — the coordinate `w = x^d` and its round trip;
* `powDeriv`, `powDeriv2`, `hasDerivAt_powDeriv`, `hasDerivAt_powChart`,
  `hasDerivAt_powChart_powDeriv` — the first and second `w`-derivatives as expressions in `x`;
* `powDop`, `powDop_eq_powDeriv2` — the operator `𝒟_d` and the normalisation constant;
* `powDD`, `powResid_eq_powDD_mul` — the second divided difference in the coordinate `w`, and
  the factorisation `powResid = (x^d - s^d)(x^d - t^d) · powDD`;
* `powDD_mem_of_powDeriv2_mem` — the mean-value bound `m/2 ≤ powDD ≤ M/2`, the exact analogue
  of `dd2_mem_of_deriv2_mem` and, like it, valid **at the nodes too** and hence uniform as the
  nodes coalesce;
* `exists_powResid_bound` — the mean-value remainder
  `powResid = powDeriv2 ξ / 2 · (x^d - s^d)(x^d - t^d)`.

Nothing here mentions the singular endpoint family, the graph `H`, or any object of Section 5; the
statements are for a bare pair of derivatives on a compact interval `[a,b]` with `a > 0`.
-/

namespace UpperTailOptimizers

/-! ## The interpolant in the basis `{1, x^d}` and its residual -/

/-- **The `x^d` coefficient** of the interpolant of `φ` in the basis `{1, x^d}` at the nodes
`s, t`: `B = (φ(t) - φ(s))/(t^d - s^d)`.  This is `eq:moment-interpolation` read as
`I_h^xF = A + Bx^d`; `KKTFamily.gCoefB` (`SingularEndpoint/AuxiliaryLagrangian/TailScalar.lean`) is the special
case `φ(u) = J̃_{p_h}(x̃u)`, `s = s_h`, `t = t_h`. -/
noncomputable def powCoefB (d : ℕ) (phi : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (phi t - phi s) / (t ^ d - s ^ d)

/-- **The constant coefficient** of the same interpolant: `A = φ(s) - B s^d`, so that the
interpolant `A + Bx^d` agrees with `φ` at the lower node by construction. -/
noncomputable def powCoefA (d : ℕ) (phi : ℝ → ℝ) (s t : ℝ) : ℝ :=
  phi s - powCoefB d phi s t * s ^ d

/-- **The interpolation residual** `R_h^xφ = φ - A - Bx^d` of `eq:moment-interpolation`. -/
noncomputable def powResid (d : ℕ) (phi : ℝ → ℝ) (s t x : ℝ) : ℝ :=
  phi x - powCoefA d phi s t - powCoefB d phi s t * x ^ d

/-- The residual vanishes at the **lower** node.  This is the definition of `A`, so no
hypothesis at all is needed. -/
theorem powResid_left (d : ℕ) (phi : ℝ → ℝ) (s t : ℝ) : powResid d phi s t s = 0 := by
  simp only [powResid, powCoefA]
  ring

/-- The residual vanishes at the **upper** node.  Here the definition of `B` is used, so the
two nodes must be separated in the `w`-coordinate: `0 ≤ s < t` and `d ≠ 0` give
`s^d < t^d`. -/
theorem powResid_right {d : ℕ} (hd : d ≠ 0) (phi : ℝ → ℝ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) : powResid d phi s t t = 0 := by
  have hlt : s ^ d < t ^ d := pow_lt_pow_left₀ hst hs hd
  have hne : t ^ d - s ^ d ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
  have hkey : powCoefB d phi s t * (t ^ d - s ^ d) = phi t - phi s :=
    div_mul_cancel₀ _ hne
  simp only [powResid, powCoefA]
  linarith

/-! ## The coordinate `w = x^d` -/

/-- **A function of `x` read as a function of `w = x^d`**: `powChart d φ w = φ (w^{1/d})`.
On `w > 0` this is the substitution `F̂(w,z) = F(w^{1/d},z^{1/d})` of the proof of
`lem:central-kernel-bound`, in one variable, under which the
interpolation `eq:moment-interpolation` becomes ordinary linear interpolation at the nodes
`s^d`, `t^d`.  The inverse map is `Real.rpow` with exponent `(d : ℝ)⁻¹`. -/
noncomputable def powChart (d : ℕ) (phi : ℝ → ℝ) (w : ℝ) : ℝ := phi (w ^ ((d : ℝ)⁻¹))

/-- The round trip: on `x ≥ 0` the chart undoes the `d`-th power. -/
theorem powChart_pow {d : ℕ} (hd : d ≠ 0) (phi : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    powChart d phi (x ^ d) = phi x := by
  rw [powChart, Real.pow_rpow_inv_natCast hx hd]

/-- The chart maps `Set.Icc (a^d) (b^d)` back into `Set.Icc a b`, is inverse to `x ↦ x^d`
there, and is positive.  The elementary bookkeeping behind every interval hypothesis below. -/
private theorem chart_mem_Icc {d : ℕ} (hd : d ≠ 0) {a b w : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hw : w ∈ Set.Icc (a ^ d) (b ^ d)) :
    w ^ ((d : ℝ)⁻¹) ∈ Set.Icc a b ∧ (w ^ ((d : ℝ)⁻¹)) ^ d = w ∧ 0 < w ^ ((d : ℝ)⁻¹) := by
  have hw0 : (0 : ℝ) < w := lt_of_lt_of_le (pow_pos ha d) hw.1
  have hb0 : (0 : ℝ) ≤ b := ha.le.trans hab
  have hlow : a ≤ w ^ ((d : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (pow_nonneg ha.le d) hw.1 (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast ha.le hd] at h
  have hhigh : w ^ ((d : ℝ)⁻¹) ≤ b := by
    have h := Real.rpow_le_rpow hw0.le hw.2 (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast hb0 hd] at h
  exact ⟨⟨hlow, hhigh⟩, Real.rpow_inv_natCast_pow hw0.le hd, Real.rpow_pos_of_pos hw0 _⟩

/-! ## The derivative with respect to `w = x^d` -/

/-- **The first derivative with respect to `w = x^d`**, written as an expression in `x`: if
`φ' = φ₁` then `dφ/dw = φ₁(x) / (d x^{d-1})`.  This is the operator appearing in
`𝒟_d`. -/
noncomputable def powDeriv (d : ℕ) (phi1 : ℝ → ℝ) (x : ℝ) : ℝ := phi1 x / ((d : ℝ) * x ^ (d - 1))

/-- **The second derivative with respect to `w = x^d`**, written as an expression in `x`:
applying `powDeriv` twice and clearing the quotient rule gives

  `d²φ/dw² = (x φ₂(x) - (d-1) φ₁(x)) / (d² x^{2d-1})`.

Equivalently `(φ₂(x) - (d-1)/x · φ₁(x)) / (d² x^{2d-2})`, which is `𝒟_d` up to the
factor `d² x^{2d-2}/2` recorded in `powDop_eq_powDeriv2`. -/
noncomputable def powDeriv2 (d : ℕ) (phi1 phi2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  (x * phi2 x - ((d : ℝ) - 1) * phi1 x) / ((d : ℝ) ^ 2 * x ^ (2 * d - 1))

/-- The **`x`-derivative** of `powDeriv`, by the quotient rule.  Only this intermediate value
is needed: composing it with the chart in `hasDerivAt_powChart_powDeriv` produces `powDeriv2`.
The degree is symbolic, so the two powers are reduced to the single atom `x^{d-2}`. -/
theorem hasDerivAt_powDeriv {d : ℕ} (hd : 2 ≤ d) {phi1 phi2 : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (h : HasDerivAt phi1 (phi2 x) x) :
    HasDerivAt (powDeriv d phi1)
      ((x * phi2 x - ((d : ℝ) - 1) * phi1 x) / ((d : ℝ) * x ^ d)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  have hpow : HasDerivAt (fun y : ℝ => y ^ (d - 1)) (((d : ℝ) - 1) * x ^ (d - 2)) x := by
    have hp := hasDerivAt_pow (d - 1) x
    rw [hcast, show d - 1 - 1 = d - 2 from by omega] at hp
    exact hp
  have hne : (d : ℝ) * x ^ (d - 1) ≠ 0 := by positivity
  have hq : HasDerivAt (powDeriv d phi1)
      ((phi2 x * ((d : ℝ) * x ^ (d - 1))
          - phi1 x * ((d : ℝ) * (((d : ℝ) - 1) * x ^ (d - 2))))
        / ((d : ℝ) * x ^ (d - 1)) ^ 2) x :=
    h.div (hpow.const_mul ((d : ℝ))) hne
  refine hq.congr_deriv ?_
  have hX : x ^ (d - 2) ≠ 0 := pow_ne_zero _ hx0
  rw [show x ^ (d - 1) = x ^ (d - 2) * x from by rw [← pow_succ]; congr 1; omega,
    show x ^ d = x ^ (d - 2) * x ^ 2 from by rw [← pow_add]; congr 1; omega]
  field_simp

/-- **The chain rule for the chart.**  If `ψ` has derivative `ψ₁ x` at `x > 0` then
`powChart d ψ` has derivative `powDeriv d ψ₁ x` at `x^d`.  Proof: `w ↦ w^{1/d}` has derivative
`(1/d) w^{1/d - 1}` at `w = x^d > 0`, and `(x^d)^{1/d - 1} = x / x^d = x^{1-d}`. -/
theorem hasDerivAt_powChart {d : ℕ} (hd : d ≠ 0) {psi psi1 : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (h : HasDerivAt psi (psi1 x) x) :
    HasDerivAt (powChart d psi) (powDeriv d psi1 x) (x ^ d) := by
  have hxd : (0 : ℝ) < x ^ d := pow_pos hx d
  have hroot : (x ^ d) ^ ((d : ℝ)⁻¹) = x := Real.pow_rpow_inv_natCast hx.le hd
  have hg : HasDerivAt (fun w : ℝ => w ^ ((d : ℝ)⁻¹))
      ((d : ℝ)⁻¹ * (x ^ d) ^ ((d : ℝ)⁻¹ - 1)) (x ^ d) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hxd))
  have h' : HasDerivAt psi (psi1 x) ((x ^ d) ^ ((d : ℝ)⁻¹)) := by rw [hroot]; exact h
  have hcomp := HasDerivAt.comp (x ^ d) h' hg
  have hfun : (psi ∘ fun w : ℝ => w ^ ((d : ℝ)⁻¹)) = powChart d psi := rfl
  rw [hfun] at hcomp
  refine hcomp.congr_deriv ?_
  have hexp : (x ^ d) ^ ((d : ℝ)⁻¹ - 1) = x / x ^ d := by
    rw [Real.rpow_sub hxd, Real.rpow_one, hroot]
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  rw [hexp, powDeriv, show x ^ d = x ^ (d - 1) * x from by rw [← pow_succ]; congr 1; omega]
  have hX : x ^ (d - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hx)
  field_simp

/-- **The second `w`-derivative of the chart.**  Combining `hasDerivAt_powDeriv` with
`hasDerivAt_powChart` at the function `powDeriv d φ₁`: the `w`-derivative of the first
`w`-derivative is `powDeriv2`. -/
theorem hasDerivAt_powChart_powDeriv {d : ℕ} (hd : 2 ≤ d) {phi1 phi2 : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (h : HasDerivAt phi1 (phi2 x) x) :
    HasDerivAt (powChart d (powDeriv d phi1)) (powDeriv2 d phi1 phi2 x) (x ^ d) := by
  have hd0 : d ≠ 0 := by omega
  have key := hasDerivAt_powChart (psi := powDeriv d phi1)
    (psi1 := fun y : ℝ => (y * phi2 y - ((d : ℝ) - 1) * phi1 y) / ((d : ℝ) * y ^ d)) hd0 hx
    (hasDerivAt_powDeriv hd hx h)
  have hval : powDeriv d
      (fun y : ℝ => (y * phi2 y - ((d : ℝ) - 1) * phi1 y) / ((d : ℝ) * y ^ d)) x
      = powDeriv2 d phi1 phi2 x := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      have : 0 < d := by omega
      exact_mod_cast this
    have hX : x ^ d ≠ 0 := pow_ne_zero _ (ne_of_gt hx)
    have hY : x ^ (d - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hx)
    rw [powDeriv, powDeriv2,
      show x ^ (2 * d - 1) = x ^ d * x ^ (d - 1) from by rw [← pow_add]; congr 1; omega]
    field_simp
  rw [← hval]
  exact key

/-! ## The coalescing operator -/

/-- **The coalescing operator `𝒟_d`** (not named in the paper; see the module docstring):

  `𝒟_d F = ½ (F''(x) - (d-1)/x · F'(x))`,

the value of `R_0^xF(x)/(x - u_*)^2` at the coalescing limit. -/
noncomputable def powDop (d : ℕ) (phi1 phi2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  (phi2 x - ((d : ℝ) - 1) / x * phi1 x) / 2

/-- **The correspondence between `𝒟_d` and `½∂_w²`, and the normalising constant.**  For
`x > 0`,

  `𝒟_d F = (d² x^{2d-2} / 2) · (d²F/dw²)`.

The residual proved below is `powDeriv2 ξ / 2` times `(x^d - s^d)(x^d - t^d)`, while `𝒟_d`
normalises by `(x - u_*)^2`; since `(x^d - u_*^d)/(x - u_*) → d u_*^{d-1}` at coalescence, the
two differ exactly by the factor `d² x^{2d-2}` recorded here.  It is this identity that makes
the constant `Θ_0(u_*,u_*) = d^3/4` of `lem:central-kernel-bound` checkable
without revisiting the change of
variable. -/
theorem powDop_eq_powDeriv2 {d : ℕ} (hd : 2 ≤ d) (phi1 phi2 : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    powDop d phi1 phi2 x = (d : ℝ) ^ 2 * x ^ (2 * d - 2) / 2 * powDeriv2 d phi1 phi2 x := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hX : x ^ (2 * d - 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hx)
  rw [powDop, powDeriv2,
    show x ^ (2 * d - 1) = x ^ (2 * d - 2) * x from by rw [← pow_succ]; congr 1; omega]
  field_simp

/-! ## The second divided difference in the coordinate `w` -/

/-- **The second divided difference of `φ` in the coordinate `w = x^d`**: `Interp2`'s total
`dd2` applied to `powChart d φ` at the nodes `s^d, t^d`, evaluated at `x^d`.

Like `dd2` it is *total* — no division by zero occurs at the nodes — so the bound
`powDD_mem_of_powDeriv2_mem` survives the coalescence `t - s ↓ 0` verbatim. -/
noncomputable def powDD (d : ℕ) (phi : ℝ → ℝ) (s t x : ℝ) : ℝ :=
  dd2 (powChart d phi) (s ^ d) (t ^ d) (x ^ d)

/-- **The factorisation of the residual.**  For `0 ≤ s < t` and `0 ≤ x`,

  `powResid d φ s t x = (x^d - s^d)(x^d - t^d) · powDD d φ s t x`.

This is `dd2_factor` (`SingularEndpoint/AuxiliaryLagrangian/Interp2.lean`) read through the chart: `dd2_factor` is the
Newton form of `powChart d φ` at the nodes `s^d, t^d`, and its linear part is exactly the
interpolant `A + Bx^d`.  No differentiability is used. -/
theorem powResid_eq_powDD_mul {d : ℕ} (hd : d ≠ 0) (phi : ℝ → ℝ) {s t x : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hst : s < t) :
    powResid d phi s t x = (x ^ d - s ^ d) * (x ^ d - t ^ d) * powDD d phi s t x := by
  have hlt : s ^ d < t ^ d := pow_lt_pow_left₀ hst hs hd
  have hne : t ^ d - s ^ d ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
  have hkey : (t ^ d - s ^ d) * dslope (powChart d phi) (s ^ d) (t ^ d) = phi t - phi s := by
    have hsm := sub_mul_dslope (powChart d phi) (s ^ d) (t ^ d)
    rwa [powChart_pow hd phi ht, powChart_pow hd phi hs] at hsm
  have hdsl : dslope (powChart d phi) (s ^ d) (t ^ d) = powCoefB d phi s t := by
    rw [powCoefB, eq_div_iff hne]
    linear_combination hkey
  have hfac := dd2_factor (powChart d phi) (s ^ d) (t ^ d) (x ^ d)
  rw [powChart_pow hd phi hx, powChart_pow hd phi hs, hdsl] at hfac
  simp only [powResid, powCoefA, powDD]
  linear_combination hfac

/-! ## The mean-value remainder -/

/-- **The mean-value theorem for the divided difference in `w`.**  If `φ → φ₁ → φ₂` is a chain
of derivatives on `Set.Icc a b` with `0 < a`, and `s < t` are two points of that interval, then
for every `x ∈ Set.Icc a b` there is a `ξ ∈ Set.Icc a b` with

  `powDD d φ s t x = powDeriv2 d φ₁ φ₂ ξ / 2`.

This is `exists_dd2_eq_deriv2_half` (`SingularEndpoint/AuxiliaryLagrangian/Interp2.lean`) applied to `powChart d φ` on
`Set.Icc (a^d) (b^d)`, whose derivative chain is supplied by `hasDerivAt_powChart` and
`hasDerivAt_powChart_powDeriv`; the mean value `ξ` is pulled back through the chart. -/
theorem exists_powDD_eq_powDeriv2_half {d : ℕ} (hd : 2 ≤ d) {phi phi1 phi2 : ℝ → ℝ}
    {a b : ℝ} (ha : 0 < a)
    (hphi : ∀ y ∈ Set.Icc a b, HasDerivAt phi (phi1 y) y)
    (hphi1 : ∀ y ∈ Set.Icc a b, HasDerivAt phi1 (phi2 y) y)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s < t)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, powDD d phi s t x = powDeriv2 d phi1 phi2 ξ / 2 := by
  have hd0 : d ≠ 0 := by omega
  have hab : a ≤ b := hs.1.trans hs.2
  -- the two derivative chains, transported to the coordinate `w`
  have hF : ∀ w ∈ Set.Icc (a ^ d) (b ^ d),
      HasDerivAt (powChart d phi) (powChart d (powDeriv d phi1) w) w := by
    intro w hw
    obtain ⟨hmem, hpow, hpos⟩ := chart_mem_Icc hd0 ha hab hw
    have h := hasDerivAt_powChart hd0 hpos (hphi _ hmem)
    rw [hpow] at h
    exact h
  have hF1 : ∀ w ∈ Set.Icc (a ^ d) (b ^ d),
      HasDerivAt (powChart d (powDeriv d phi1)) (powChart d (powDeriv2 d phi1 phi2) w) w := by
    intro w hw
    obtain ⟨hmem, hpow, hpos⟩ := chart_mem_Icc hd0 ha hab hw
    have h := hasDerivAt_powChart_powDeriv hd hpos (hphi1 _ hmem)
    rw [hpow] at h
    exact h
  -- the nodes and the evaluation point, transported to the coordinate `w`
  have hmono : ∀ {y : ℝ}, y ∈ Set.Icc a b → y ^ d ∈ Set.Icc (a ^ d) (b ^ d) := by
    intro y hy
    exact ⟨pow_le_pow_left₀ ha.le hy.1 d, pow_le_pow_left₀ (ha.le.trans hy.1) hy.2 d⟩
  have hstd : s ^ d < t ^ d := pow_lt_pow_left₀ hst (ha.le.trans hs.1) hd0
  obtain ⟨W, hW, hval⟩ :=
    exists_dd2_eq_deriv2_half hF hF1 (hmono hs) (hmono ht) hstd (hmono hx)
  obtain ⟨hmem, _, _⟩ := chart_mem_Icc hd0 ha hab hW
  exact ⟨W ^ ((d : ℝ)⁻¹), hmem, hval⟩

/-- **The mean-value bound for `powDD` — the exact analogue of `dd2_mem_of_deriv2_mem`.**  If
`φ → φ₁ → φ₂` is a chain of derivatives on `Set.Icc a b` with `0 < a` and
`m ≤ powDeriv2 d φ₁ φ₂ ≤ M` there, then

  `m/2 ≤ powDD d φ s t x ≤ M/2`   for every `x ∈ Set.Icc a b`,

nodes included.  Since `powDD` never divides by zero, the bound is uniform as `t - s ↓ 0`;
this mean-value form replaces the integral representation of the second divided difference
`F̂[s_h^d,x^d,t_h^d;y^d]` and its bound `|F̂[s_h^d,x^d,t_h^d;y^d]| ≤ ½sup|∂_w²F̂|` in the
proof of `lem:central-kernel-bound`. -/
theorem powDD_mem_of_powDeriv2_mem {d : ℕ} (hd : 2 ≤ d) {phi phi1 phi2 : ℝ → ℝ}
    {a b m M : ℝ} (ha : 0 < a)
    (hphi : ∀ y ∈ Set.Icc a b, HasDerivAt phi (phi1 y) y)
    (hphi1 : ∀ y ∈ Set.Icc a b, HasDerivAt phi1 (phi2 y) y)
    (hm : ∀ y ∈ Set.Icc a b, m ≤ powDeriv2 d phi1 phi2 y)
    (hM : ∀ y ∈ Set.Icc a b, powDeriv2 d phi1 phi2 y ≤ M)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s < t)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    m / 2 ≤ powDD d phi s t x ∧ powDD d phi s t x ≤ M / 2 := by
  obtain ⟨ξ, hξ, hval⟩ := exists_powDD_eq_powDeriv2_half hd ha hphi hphi1 hs ht hst hx
  rw [hval]
  exact ⟨by linarith [hm ξ hξ], by linarith [hM ξ hξ]⟩

/-- **The mean-value remainder of the interpolation in `{1, x^d}` — the target of the file.**
For a chain of derivatives `φ → φ₁ → φ₂` on `Set.Icc a b` with `0 < a`, nodes `s < t` in the
interval and any `x` in the interval, there is a `ξ ∈ Set.Icc a b` with

  `powResid d φ s t x = powDeriv2 d φ₁ φ₂ ξ / 2 · (x^d - s^d)(x^d - t^d)`.

`powResid_eq_powDD_mul` factors the residual and `exists_powDD_eq_powDeriv2_half` evaluates the
cofactor.  The Lean counterpart of the bound the paper actually uses,
`|F̂[s_h^d,x^d,t_h^d;y^d]| ≤ ½sup|∂_w²F̂|`, is the two-sided `powDD_mem_of_powDeriv2_mem`. -/
theorem exists_powResid_bound {d : ℕ} (hd : 2 ≤ d) {phi phi1 phi2 : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a)
    (hphi : ∀ y ∈ Set.Icc a b, HasDerivAt phi (phi1 y) y)
    (hphi1 : ∀ y ∈ Set.Icc a b, HasDerivAt phi1 (phi2 y) y)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s < t)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b,
      powResid d phi s t x
        = powDeriv2 d phi1 phi2 ξ / 2 * ((x ^ d - s ^ d) * (x ^ d - t ^ d)) := by
  have hd0 : d ≠ 0 := by omega
  obtain ⟨ξ, hξ, hval⟩ := exists_powDD_eq_powDeriv2_half hd ha hphi hphi1 hs ht hst hx
  refine ⟨ξ, hξ, ?_⟩
  rw [powResid_eq_powDD_mul hd0 phi (ha.le.trans hs.1) (ha.le.trans ht.1)
    (ha.le.trans hx.1) hst, hval]
  ring

end UpperTailOptimizers
