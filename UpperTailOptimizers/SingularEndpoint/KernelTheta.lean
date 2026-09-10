import UpperTailOptimizers.SingularEndpoint.Contact
import UpperTailOptimizers.SingularEndpoint.KernelInterp

/-!
# The corner constant of `lem:central-kernel-bound` (Section 7, `paper/singular_endpoint.tex`)

The proof of `lem:central-kernel-bound`, which absorbs the interpolation decomposition, closes by evaluating the *coalescing*
interpolation remainder of the law kernel at the corner of the central square.  The paper works in
the coordinates `w = x^d`, `z = y^d`, writing `K̂_0(w,z) := K_0(w^{1/d},z^{1/d})`, and asserts

  `Θ_0(u_*,u_*) = ((du_*^{d-1})^4/4)·∂²_w∂²_z K̂_0|_{(u_*^d,u_*^d)} = u_*^4Γ_d^{(4)}(r_*)/4
  = d³/4`,

where `K_0(x,y) = J̃_{p_*}(xy)` and `Θ_h` is the paper's corner quotient.  In the original
variable, one coalesced pair of nodes contributes exactly the
operator

  `𝒟_dF := ½(F''(u_*) - (d-1)/u_* · F'(u_*))`  (already `powDop`; the paper keeps only its `w`-coordinate form `½∂²_w` up to
  the chain-rule factor `(du_*^{d-1})²`),

so the corner value is the iterated-operator value
`𝒟_{d,x}𝒟_{d,y}K_0(x,y)|_{(u_*,u_*)} = d³/4`.  **This file proves that iterated-operator
value.**  Its two public targets are

* `powDopOf_thetaSliceD` — the self-contained calculus lemma behind the display: for a chain
  of derivatives `F → F₁ → F₂ → F₃ → F₄` on an open interval containing `r_* = u_*²` whose
  first three derivatives vanish at `r_*`, the inner slice
  `G(y) = 𝒟_{d,x}K(·,y)|_{x=u_*} = ½(y²F₂(u_*y) - (d-1)/u_* · yF₁(u_*y))` (`thetaSliceD`)
  satisfies `𝒟_dG|_{u_*} = u_*^4F₄(r_*)/4`.  Both `G'(u_*) = 0` and `G''(u_*) = u_*^4F₄(r_*)/2`
  come out of the computation; the arithmetic is separated from the entropy exactly as the
  paper separates them;
* `powDopOf_powDopOf_kernel` — the specialisation at `F = Γ_d`, i.e. the displayed value

  `𝒟_{d,x}𝒟_{d,y}J_{p_*}(xy)|_{(u_*,u_*)} = d³/4`,

  together with its family form `KKTFamily.powDopOf_powDopOf_kernel_zero` for the kernel
  `B.kernel 0` of `SingularEndpoint/KernelInterp.lean` (`B.p 0 = p_*` by `p_zero`).

## The route

`powDopOf d F x = powDop d (deriv F) (deriv (deriv F)) x` is the operator `𝒟_d` applied to an
*honest* function through Lean's `deriv`, so nothing below assumes a derivative chain that is
not proved.  Three steps, in the order of the paper's own argument.

1. **`𝒟_d` annihilates the trivial part** ("The constant and `β_dwz` have zero mixed
  derivative of order `(2,2)`").  `powDop_const` and `powDop_pow`: the
   constant and `β_d(xy)^d` of the singular endpoint decomposition of `K_0` contribute nothing, in each
   variable separately, because `(xy)^d = x^dy^d` makes the second one a monomial in the
   running variable.  Both are stated for the *derivative chain* of the function, since that is
   what `powDop` consumes; `powDop_pow` needs `x ≠ 0` and `2 ≤ d` (the exponent `d - 2` is a
   natural-number subtraction, so `x^{d-1} = x^{d-2}·x` is a hypothesis-carrying rewrite).
2. **The core computation** (`powDopOf_thetaSliceD`).  Stated for an abstract chain, not for
   `Γ_d`: `thetaSliceD1`, `thetaSliceD2` are `G'` and `G''` written out, and
   `hasDerivAt_thetaSliceD`, `hasDerivAt_thetaSliceD1` prove that they *are* the derivatives,
   so the conclusion is about `deriv` and `deriv (deriv ·)` and not about hand-written
   surrogates.  Every term carrying `F₁`, `F₂` or `F₃` dies at `y = u_*` because `u_*y = r_*`
   there.
3. **The specialisation.**  `powDopOf_kernel_slice` performs the inner `𝒟_{d,y}` on the kernel
   slice `y ↦ J_{p_*}(xy)`, whose derivative chain is `x·J_{p_*}'(xy)`, `x²·J_{p_*}''(xy)`; the
   split `J_{p_*}' = 𝓛_* + γ_*z^{d-1}`, `J_{p_*}'' = 𝓛_*' + γ_*(d-1)z^{d-2}` and step 1 reduce
   it to `thetaSliceD d u_* 𝓛_* 𝓛_*'`.  The chain `Γ_d → 𝓛_* → 𝓛_*' → 𝓛_*'' → 𝓛_*'''`
   (`hasDerivAt_Gam`, `hasDerivAt_Lstar`, `hasDerivAt_Lstar1`, `hasDerivAt_Lstar2`), the triple
   contact `Lstar_rStar`, `Lstar1_rStar`, `Lstar2_rStar` and the non-degeneracy
   `Lstar3_rStar : Γ_d^{(4)}(r_*) = d⁵/(d-1)²` then give
   `u_*^4·d⁵/(d-1)²/4 = ((d-1)/d)²·d⁵/(d-1)²/4 = d³/4`.

## What is not here

The uniform corner-error bound `‖Θ_h - d³/4‖_{L^∞(𝓝_ρ²)} ≤ a/8` of
`lem:central-kernel-bound` is not here, and neither is the identification of the value computed here with the
coalescing limit of `KKTFamily.kernelTheta` (`SingularEndpoint/KernelInterp.lean`), i.e. with the
paper's `Θ_0(u_*,u_*)`.  Both are `SingularEndpoint/KernelError.lean`
(`KKTFamily.exists_kernelTheta_error`, with `thetaV_theta_value` transporting the
value proved here into the chart).  The paper obtains them from "the joint continuity of
`Θ_h(x,y)` at `(0,u_*,u_*)`" ; formalising that needs a derivative chain for
the map `z ↦ powDD d (K_h(z,·)) s_h t_h y` — a divided difference of a divided difference — so
that `powDD_mem_of_powDeriv2_mem` can be applied a second time, together with uniform bounds
on `J_{p_h}'''` and `J_{p_h}^{(4)}` near `r_*`, and that is what that file supplies.  Nothing
below is stated conditionally: every theorem in this file is an unconditional identity about
`deriv`.

## Contents

* `powDopOf` — the operator `𝒟_d` applied to a function through `deriv`, with `powDop_congr`,
  `powDop_add` and `powDopOf_congr_nhds` (a local-in-`𝓝` congruence, all `𝒟_d` reads);
* `powDop_const`, `powDop_pow` — step 1, `𝒟_d` annihilates the constant and `c·z^d`;
* `thetaSliceD` — the inner slice `𝒟_{d,x}K(·,y)|_{x=u_*}` of a kernel `K(x,y) = F(xy)`;
* `powDopOf_thetaSliceD` — step 2, the core: `𝒟_d(thetaSliceD)|_{u_*} = u_*^4F₄(u_*²)/4`;
* `powDopOf_kernel_slice` — step 3a, the inner operator applied to `y ↦ J_{p_*}(xy)`;
* `powDopOf_powDopOf_kernel`, `KKTFamily.powDopOf_powDopOf_kernel_zero` — step 3b,
  **the corner constant `d³/4`**.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Filter Topology

/-! ## `𝒟_d` applied to a function

`powDop` (`SingularEndpoint/PowInterp.lean`) takes the two derivatives of `F` as *data*, which is what
the mean-value arguments there need.  Here the derivatives are the honest `deriv`s, so that the
corner constant is a statement about `J_{p_*}` and nothing else. -/

/-- **The coalesced-node operator `𝒟_dF = ½(F''(x) - (d-1)/x · F'(x))`** — the `x`-variable
form of the paper's `½∂²_w` at `w = x^d` up to the chain-rule factor `(dx^{d-1})²` — applied to a function through Lean's
`deriv`. -/
noncomputable def powDopOf (d : ℕ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  powDop d (deriv F) (deriv (deriv F)) x

/-- `powDop` reads its two arguments **only at the evaluation point**, so two derivative chains
agreeing there give the same value.  This is what lets the singular endpoint decomposition of the kernel
be substituted one term at a time. -/
theorem powDop_congr (d : ℕ) {phi1 phi2 psi1 psi2 : ℝ → ℝ} {x : ℝ} (h1 : phi1 x = psi1 x)
    (h2 : phi2 x = psi2 x) : powDop d phi1 phi2 x = powDop d psi1 psi2 x := by
  simp only [powDop, h1, h2]

/-- **`𝒟_d` is additive in the function**, i.e. in its derivative chain. -/
theorem powDop_add (d : ℕ) (phi1 phi2 psi1 psi2 : ℝ → ℝ) (x : ℝ) :
    powDop d (fun z => phi1 z + psi1 z) (fun z => phi2 z + psi2 z) x
      = powDop d phi1 phi2 x + powDop d psi1 psi2 x := by
  simp only [powDop]
  ring

/-- If two functions agree near `x` then `𝒟_d` does not distinguish them: both `deriv` and
`deriv (deriv ·)` are local. -/
theorem powDopOf_congr_nhds (d : ℕ) {F G : ℝ → ℝ} {x : ℝ} (h : F =ᶠ[𝓝 x] G) :
    powDopOf d F x = powDopOf d G x := by
  simp only [powDopOf, powDop, h.deriv_eq, h.deriv.deriv_eq]

/-! ## Step 1: `𝒟_d` annihilates the trivial part

"The constant and `β_dwz` have zero mixed derivative of order `(2,2)`" — in the original
variables, the constant and `β_d(xy)^d` of the singular endpoint decomposition of `K_0(x,y) = J_{p_*}(xy)`
are annihilated by `𝒟_d` in each variable.  Since `(xy)^d = x^dy^d`, the second one is, in the
running variable, a plain monomial `c·z^d`; its derivative chain is `c·d·z^{d-1}`,
`c·d(d-1)·z^{d-2}`. -/

/-- **`𝒟_d` annihilates a constant**: its derivative chain is `0, 0`.  No hypothesis. -/
theorem powDop_const (d : ℕ) (x : ℝ) : powDop d (fun _ => 0) (fun _ => 0) x = 0 := by
  simp only [powDop]
  ring

/-- **`𝒟_d` annihilates `z ↦ c·z^d`** at every `x ≠ 0`, the second half of step 1: with
`φ₁ = c·d·z^{d-1}` and `φ₂ = c·d(d-1)·z^{d-2}`,

  `φ₂(x) - (d-1)/x · φ₁(x) = c·d(d-1)x^{d-2} - c·d(d-1)x^{d-2} = 0`.

The degree is symbolic, so `x^{d-1} = x^{d-2}·x` is where `2 ≤ d` is used: for `d < 2` the
natural-number subtractions truncate and the identity is false. -/
theorem powDop_pow {d : ℕ} (hd : 2 ≤ d) (c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    powDop d (fun z => c * (d : ℝ) * z ^ (d - 1))
      (fun z => c * (d : ℝ) * ((d : ℝ) - 1) * z ^ (d - 2)) x = 0 := by
  have hpow : x ^ (d - 1) = x ^ (d - 2) * x := by
    rw [← pow_succ, show d - 2 + 1 = d - 1 from by omega]
  have hkey : ((d : ℝ) - 1) / x * (c * (d : ℝ) * (x ^ (d - 2) * x))
      = c * (d : ℝ) * ((d : ℝ) - 1) * x ^ (d - 2) := by
    rw [div_mul_eq_mul_div, div_eq_iff hx]
    ring
  simp only [powDop, hpow, hkey]
  ring

/-! ## Step 2: the coalescing corner of an abstract kernel `K(x,y) = F(xy)`

For `K(x,y) = F(xy)` the inner operator `𝒟_{d,x}K(·,y)|_{x=u}` is, as a function of the frozen
variable `y`,

  `G(y) = ½(y²F''(uy) - (d-1)/u · yF'(uy))`,

since `∂_xK(x,y) = yF'(xy)` and `∂_x²K(x,y) = y²F''(xy)`.  `thetaSliceD1` and `thetaSliceD2`
are `G'` and `G''`, computed by the product and chain rules; they are private because only the
core theorem consumes them, but they are proved to *be* the derivatives, so the core theorem
speaks about `deriv`. -/

/-- **The inner slice** `G(y) = 𝒟_{d,x}K(·,y)|_{x=u}` of a kernel `K(x,y) = F(xy)`, written
through the derivative chain `F' = F₁`, `F'' = F₂`.  It is `powDop d (fun _ => y·F₁(uy))
(fun _ => y²·F₂(uy)) u` — the operator acts in the *first* variable, at the point `u`. -/
noncomputable def thetaSliceD (d : ℕ) (u : ℝ) (F1 F2 : ℝ → ℝ) (y : ℝ) : ℝ :=
  (y ^ 2 * F2 (u * y) - ((d : ℝ) - 1) / u * (y * F1 (u * y))) / 2

/-- `G'`, the `y`-derivative of `thetaSliceD` (`hasDerivAt_thetaSliceD`). -/
private noncomputable def thetaSliceD1 (d : ℕ) (u : ℝ) (F1 F2 F3 : ℝ → ℝ) (y : ℝ) : ℝ :=
  (2 * y * F2 (u * y) + y ^ 2 * u * F3 (u * y)
    - ((d : ℝ) - 1) / u * (F1 (u * y) + y * u * F2 (u * y))) / 2

/-- `G''`, the second `y`-derivative of `thetaSliceD` (`hasDerivAt_thetaSliceD1`).  It does
not involve `F₁`: that term has been differentiated away. -/
private noncomputable def thetaSliceD2 (d : ℕ) (u : ℝ) (F2 F3 F4 : ℝ → ℝ) (y : ℝ) : ℝ :=
  (2 * F2 (u * y) + 4 * y * u * F3 (u * y) + y ^ 2 * u ^ 2 * F4 (u * y)
    - ((d : ℝ) - 1) / u * (2 * u * F2 (u * y) + y * u ^ 2 * F3 (u * y))) / 2

/-- `G' = thetaSliceD1`: the product rule on `y²F₂(uy)` and `yF₁(uy)`, with the chain rule
`(F(u·))' = u·F'(u·)` inside. -/
private theorem hasDerivAt_thetaSliceD {d : ℕ} {F1 F2 F3 : ℝ → ℝ} {u y : ℝ}
    (h1 : HasDerivAt F1 (F2 (u * y)) (u * y)) (h2 : HasDerivAt F2 (F3 (u * y)) (u * y)) :
    HasDerivAt (thetaSliceD d u F1 F2) (thetaSliceD1 d u F1 F2 F3 y) y := by
  have hmul : HasDerivAt (fun z : ℝ => u * z) u y := by
    simpa using (hasDerivAt_id y).const_mul u
  have hA : HasDerivAt (fun z : ℝ => F2 (u * z)) (F3 (u * y) * u) y := h2.comp y hmul
  have hB : HasDerivAt (fun z : ℝ => F1 (u * z)) (F2 (u * y) * u) y := h1.comp y hmul
  have hid : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have hP : HasDerivAt (fun z : ℝ => z ^ 2 * F2 (u * z))
      (2 * y * F2 (u * y) + y ^ 2 * (F3 (u * y) * u)) y := hsq.mul hA
  have hQ : HasDerivAt (fun z : ℝ => z * F1 (u * z))
      (1 * F1 (u * y) + y * (F2 (u * y) * u)) y := hid.mul hB
  have hfin := (hP.sub (hQ.const_mul (((d : ℝ) - 1) / u))).div_const 2
  refine hfin.congr_deriv ?_
  simp only [thetaSliceD1]
  ring

/-- `G'' = thetaSliceD2`, one differentiation further. -/
private theorem hasDerivAt_thetaSliceD1 {d : ℕ} {F1 F2 F3 F4 : ℝ → ℝ} {u y : ℝ}
    (h1 : HasDerivAt F1 (F2 (u * y)) (u * y)) (h2 : HasDerivAt F2 (F3 (u * y)) (u * y))
    (h3 : HasDerivAt F3 (F4 (u * y)) (u * y)) :
    HasDerivAt (thetaSliceD1 d u F1 F2 F3) (thetaSliceD2 d u F2 F3 F4 y) y := by
  have hmul : HasDerivAt (fun z : ℝ => u * z) u y := by
    simpa using (hasDerivAt_id y).const_mul u
  have hA : HasDerivAt (fun z : ℝ => F2 (u * z)) (F3 (u * y) * u) y := h2.comp y hmul
  have hB : HasDerivAt (fun z : ℝ => F1 (u * z)) (F2 (u * y) * u) y := h1.comp y hmul
  have hC : HasDerivAt (fun z : ℝ => F3 (u * z)) (F4 (u * y) * u) y := h3.comp y hmul
  have hid : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have hlin : HasDerivAt (fun z : ℝ => 2 * z) 2 y := by simpa using hid.const_mul (2 : ℝ)
  have hT1 : HasDerivAt (fun z : ℝ => 2 * z * F2 (u * z))
      (2 * F2 (u * y) + 2 * y * (F3 (u * y) * u)) y := hlin.mul hA
  have hT2 : HasDerivAt (fun z : ℝ => z ^ 2 * u * F3 (u * z))
      (2 * y * u * F3 (u * y) + y ^ 2 * u * (F4 (u * y) * u)) y := (hsq.mul_const u).mul hC
  have hT3 : HasDerivAt (fun z : ℝ => z * u * F2 (u * z))
      (1 * u * F2 (u * y) + y * u * (F3 (u * y) * u)) y := (hid.mul_const u).mul hA
  have hfin := ((hT1.add hT2).sub ((hB.add hT3).const_mul (((d : ℝ) - 1) / u))).div_const 2
  refine hfin.congr_deriv ?_
  simp only [thetaSliceD2]
  ring

/-- **The core computation**.  Let `F → F₁ → F₂ → F₃ → F₄`
be a chain of derivatives on an open interval `(a,b)` containing `r_* = u²`, and suppose the
first three derivatives vanish there:

  `F₁(u²) = F₂(u²) = F₃(u²) = 0`.

Then the inner slice `G = thetaSliceD d u F₁ F₂` — the value `𝒟_{d,x}K(·,y)|_{x=u}` for
`K(x,y) = F(xy)` — satisfies

  `𝒟_dG|_u = u⁴F₄(u²)/4`.

Indeed `G'(u) = 0` and `G''(u) = u⁴F₄(u²)/2`: every term of `thetaSliceD1` and
`thetaSliceD2` carries `F₁`, `F₂` or `F₃` except the single term `y²u²F₄(uy)`, and at `y = u`
the argument is `u·u = u²`.  `F` itself is never used — `𝒟_d` reads only `F'` and `F''` — and
is kept as an argument to match the notation `𝒟_dF`.  Neither is `0 < u` needed: `powDop` is
total, so the paper's standing `u_* > 0` never enters. -/
theorem powDopOf_thetaSliceD {d : ℕ} {F F1 F2 F3 F4 : ℝ → ℝ} {a b u : ℝ}
    (hr : u ^ 2 ∈ Set.Ioo a b)
    (_hF : ∀ z ∈ Set.Ioo a b, HasDerivAt F (F1 z) z)
    (hF1 : ∀ z ∈ Set.Ioo a b, HasDerivAt F1 (F2 z) z)
    (hF2 : ∀ z ∈ Set.Ioo a b, HasDerivAt F2 (F3 z) z)
    (hF3 : ∀ z ∈ Set.Ioo a b, HasDerivAt F3 (F4 z) z)
    (h1 : F1 (u ^ 2) = 0) (h2 : F2 (u ^ 2) = 0) (h3 : F3 (u ^ 2) = 0) :
    powDopOf d (thetaSliceD d u F1 F2) u = u ^ 4 * F4 (u ^ 2) / 4 := by
  have huu : u * u = u ^ 2 := (sq u).symm
  have hIoo : Set.Ioo a b ∈ 𝓝 (u * u) := by
    rw [huu]
    exact Ioo_mem_nhds hr.1 hr.2
  have hnb : ∀ᶠ y in 𝓝 u, u * y ∈ Set.Ioo a b :=
    (continuous_const_mul u).continuousAt.preimage_mem_nhds hIoo
  have hu2 : u * u ∈ Set.Ioo a b := hnb.self_of_nhds
  have hEq : deriv (thetaSliceD d u F1 F2) =ᶠ[𝓝 u] thetaSliceD1 d u F1 F2 F3 := by
    filter_upwards [hnb] with y hy
    exact (hasDerivAt_thetaSliceD (hF1 _ hy) (hF2 _ hy)).deriv
  have e1 : deriv (thetaSliceD d u F1 F2) u = thetaSliceD1 d u F1 F2 F3 u :=
    (hasDerivAt_thetaSliceD (hF1 _ hu2) (hF2 _ hu2)).deriv
  have e2 : deriv (deriv (thetaSliceD d u F1 F2)) u = thetaSliceD2 d u F2 F3 F4 u := by
    rw [hEq.deriv_eq]
    exact (hasDerivAt_thetaSliceD1 (hF1 _ hu2) (hF2 _ hu2) (hF3 _ hu2)).deriv
  simp only [powDopOf, powDop, e1, e2, thetaSliceD1, thetaSliceD2, huu, h1, h2, h3]
  ring

/-! ## Step 3: the law kernel at the singular endpoint

`K_0(x,y) = J_{p_*}(xy)`.  The `y`-slice at frozen `x` has derivative chain `x·J_{p_*}'(xy)`,
`x²·J_{p_*}''(xy)`; splitting off `γ_*z^{d-1}` and `γ_*(d-1)z^{d-2}` — the derivative chain of
`β_d x^dy^d` in `y`, by `betaD_mul_d` — leaves the chain of `𝓛_* = Γ_d'`. -/

/-- **The inner operator applied to the kernel slice.**  For `0 < x, u < 1`,

  `𝒟_{d,y}J_{p_*}(x·)|_{y=u} = thetaSliceD d u 𝓛_* 𝓛_*' x`.

The two `deriv`s are computed from `hasDerivAt_Jp`, `hasDerivAt_Jp'` and the chain rule, the
second one through `Filter.EventuallyEq.deriv_eq` because `deriv (deriv ·)` reads the first
derivative on a whole neighbourhood.  The monomial part of the kernel is discarded by
`powDop_add` and `powDop_pow`; the constant part never appears, `J_{p_*}` being differentiated
before the decomposition is used. -/
theorem powDopOf_kernel_slice {d : ℕ} (hd : 2 ≤ d) {u x : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    powDopOf d (fun y => Jp (pStar d) (x * y)) u = thetaSliceD d u (Lstar d) (Lstar1 d) x := by
  have hune : u ≠ 0 := ne_of_gt hu0
  have ex1 : x * x ^ (d - 1) = x ^ d := by
    rw [mul_comm, ← pow_succ, show d - 1 + 1 = d from by omega]
  have ex2 : x ^ 2 * x ^ (d - 2) = x ^ d := by
    rw [← pow_add, show 2 + (d - 2) = d from by omega]
  have hxmul : ∀ y : ℝ, HasDerivAt (fun z : ℝ => x * z) x y := by
    intro y
    simpa using (hasDerivAt_id y).const_mul x
  have hxy : ∀ y ∈ Set.Ioo (0 : ℝ) 1, 0 < x * y ∧ x * y < 1 := by
    intro y hy
    refine ⟨mul_pos hx0 hy.1, ?_⟩
    have h := mul_lt_mul_of_pos_right hx1 hy.1
    linarith [hy.2]
  have hJ : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun z : ℝ => Jp (pStar d) (x * z)) (x * Jp' (pStar d) (x * y)) y := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hxy y hy
    have hcomp : HasDerivAt (fun z : ℝ => Jp (pStar d) (x * z)) (Jp' (pStar d) (x * y) * x) y :=
      (hasDerivAt_Jp (pStar_pos hd) (pStar_lt_one hd) hy0 hy1).comp y (hxmul y)
    exact hcomp.congr_deriv (mul_comm _ _)
  have hJ' : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun z : ℝ => x * Jp' (pStar d) (x * z)) (x * (Jp'' (x * y) * x)) y := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hxy y hy
    have hcomp : HasDerivAt (fun z : ℝ => Jp' (pStar d) (x * z)) (Jp'' (x * y) * x) y :=
      (hasDerivAt_Jp' (pStar_pos hd) (pStar_lt_one hd) hy0 hy1).comp y (hxmul y)
    exact hcomp.const_mul x
  have humem : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hu0, hu1⟩
  have hEq : deriv (fun z : ℝ => Jp (pStar d) (x * z))
      =ᶠ[𝓝 u] fun z : ℝ => x * Jp' (pStar d) (x * z) := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with y hy
    exact (hJ y hy).deriv
  have e1 : deriv (fun z : ℝ => Jp (pStar d) (x * z)) u = x * Jp' (pStar d) (x * u) :=
    (hJ u humem).deriv
  have e2 : deriv (deriv fun z : ℝ => Jp (pStar d) (x * z)) u = x * (Jp'' (x * u) * x) := by
    rw [hEq.deriv_eq]
    exact (hJ' u humem).deriv
  have ha : deriv (fun z : ℝ => Jp (pStar d) (x * z)) u
      = x * Lstar d (x * u) + betaD d * x ^ d * (d : ℝ) * u ^ (d - 1) := by
    rw [e1]
    simp only [Lstar, Fkkt]
    rw [mul_pow, ← betaD_mul_d hd, ← ex1]
    ring
  have hb : deriv (deriv fun z : ℝ => Jp (pStar d) (x * z)) u
      = x * (Lstar1 d (x * u) * x)
        + betaD d * x ^ d * (d : ℝ) * ((d : ℝ) - 1) * u ^ (d - 2) := by
    rw [e2]
    simp only [Lstar1]
    rw [mul_pow, ← betaD_mul_d hd, ← ex2]
    ring
  calc powDopOf d (fun y => Jp (pStar d) (x * y)) u
      = powDop d
          (fun z : ℝ => x * Lstar d (x * z) + betaD d * x ^ d * (d : ℝ) * z ^ (d - 1))
          (fun z : ℝ => x * (Lstar1 d (x * z) * x)
            + betaD d * x ^ d * (d : ℝ) * ((d : ℝ) - 1) * z ^ (d - 2)) u := by
        simp only [powDopOf]
        exact powDop_congr d ha hb
    _ = powDop d (fun z : ℝ => x * Lstar d (x * z))
            (fun z : ℝ => x * (Lstar1 d (x * z) * x)) u
        + powDop d (fun z : ℝ => betaD d * x ^ d * (d : ℝ) * z ^ (d - 1))
            (fun z : ℝ => betaD d * x ^ d * (d : ℝ) * ((d : ℝ) - 1) * z ^ (d - 2)) u :=
        powDop_add d _ _ _ _ u
    _ = powDop d (fun z : ℝ => x * Lstar d (x * z))
            (fun z : ℝ => x * (Lstar1 d (x * z) * x)) u := by
        rw [powDop_pow hd (betaD d * x ^ d) hune, add_zero]
    _ = thetaSliceD d u (Lstar d) (Lstar1 d) x := by
        simp only [powDop, thetaSliceD]
        rw [mul_comm u x]
        ring

/-- **The corner constant `Θ_0(u_*,u_*) = d³/4`**, the value the deferred corner-error
clause of `lem:central-kernel-bound` compares against:

  `𝒟_{d,x}𝒟_{d,y}J_{p_*}(xy)|_{(u_*,u_*)} = u_*^4Γ_d^{(4)}(r_*)/4
     = ((d-1)/d)²·d⁵/(d-1)²/4 = d³/4`.

The outer operator is applied to the honest function `x ↦ 𝒟_{d,y}K_0(x,·)|_{u_*}`, which
`powDopOf_kernel_slice` identifies with `thetaSliceD d u_* 𝓛_* 𝓛_*'` on the whole of `(0,1)`
— in particular on a neighbourhood of `u_*`, which is all `powDopOf_congr_nhds` needs.  The
vanishing hypotheses of `powDopOf_thetaSliceD` are the triple contact
`eq:endpoint-entropy-derivatives` and the remaining value is
`Lstar3_rStar : Γ_d^{(4)}(r_*) = d⁵/(d-1)²`.

This is the *value of the iterated operator*, not the coalescing limit of
`KKTFamily.kernelTheta`; that identification is `SingularEndpoint/KernelError.lean`, see the
module docstring. -/
theorem powDopOf_powDopOf_kernel {d : ℕ} (hd : 2 ≤ d) :
    powDopOf d (fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d)) (uStar d)
      = (d : ℝ) ^ 3 / 4 := by
  have h1 : (1 : ℝ) < (d : ℝ) := one_lt_d hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hslice : (fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d))
      =ᶠ[𝓝 (uStar d)] thetaSliceD d (uStar d) (Lstar d) (Lstar1 d) := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with x hx
    exact powDopOf_kernel_slice hd hu0 hu1 hx.1 hx.2
  have hmem : uStar d ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [uStar_sq hd]
    exact ⟨rStar_pos hd, rStar_lt_one hd⟩
  have hv1 : Lstar d (uStar d ^ 2) = 0 := by rw [uStar_sq hd]; exact Lstar_rStar hd
  have hv2 : Lstar1 d (uStar d ^ 2) = 0 := by rw [uStar_sq hd]; exact Lstar1_rStar hd
  have hv3 : Lstar2 d (uStar d ^ 2) = 0 := by rw [uStar_sq hd]; exact Lstar2_rStar hd
  have hu4 : uStar d ^ 4 = (((d : ℝ) - 1) / (d : ℝ)) ^ 2 := by
    calc uStar d ^ 4 = (uStar d ^ 2) ^ 2 := by ring
      _ = rStar d ^ 2 := by rw [uStar_sq hd]
      _ = (((d : ℝ) - 1) / (d : ℝ)) ^ 2 := by rw [rStar_eq]
  have hkey : (((d : ℝ) - 1) / (d : ℝ)) ^ 2 * ((d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2)
      = (d : ℝ) ^ 3 := by
    rw [div_pow, div_mul_div_comm,
      div_eq_iff (mul_ne_zero (pow_ne_zero 2 hd0) (pow_ne_zero 2 hd1))]
    ring
  calc powDopOf d (fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d)) (uStar d)
      = powDopOf d (thetaSliceD d (uStar d) (Lstar d) (Lstar1 d)) (uStar d) :=
        powDopOf_congr_nhds d hslice
    _ = uStar d ^ 4 * Lstar3 d (uStar d ^ 2) / 4 :=
        powDopOf_thetaSliceD hmem (fun _ hz => hasDerivAt_Gam hd hz.1 hz.2)
          (fun _ hz => hasDerivAt_Lstar hd hz.1 hz.2)
          (fun _ hz => hasDerivAt_Lstar1 hd hz.1 hz.2)
          (fun _ hz => hasDerivAt_Lstar2 hd hz.1 hz.2) hv1 hv2 hv3
    _ = (d : ℝ) ^ 3 / 4 := by rw [uStar_sq hd, Lstar3_rStar hd, hu4, hkey]

namespace KKTFamily

/-- **The corner constant for the family kernel at `h = 0`.**  `B.kernel 0 x y = J_{p_0}(xy)`
with `p_0 = p_*` (`KKTFamily.p_zero`), so this is `powDopOf_powDopOf_kernel` transported to
the object `SingularEndpoint/KernelInterp.lean` decomposes:

  `𝒟_{d,x}𝒟_{d,y}K_0(x,y)|_{(u_*,u_*)} = d³/4`.

It is *not* asserted here that this value is the limit of `B.kernelTheta h x y` as
`(h,x,y) → (0,u_*,u_*)`; see the module docstring. -/
theorem powDopOf_powDopOf_kernel_zero {d : ℕ} (hd : 2 ≤ d) (B : KKTFamily d) :
    powDopOf d (fun x => powDopOf d (B.kernel 0 x) (uStar d)) (uStar d) = (d : ℝ) ^ 3 / 4 := by
  have hker : ∀ x : ℝ, B.kernel 0 x = fun y => Jp (pStar d) (x * y) := by
    intro x
    funext y
    simp only [kernel, B.p_zero]
  have hfun : (fun x => powDopOf d (B.kernel 0 x) (uStar d))
      = fun x => powDopOf d (fun y => Jp (pStar d) (x * y)) (uStar d) := by
    funext x
    rw [hker x]
  rw [hfun]
  exact powDopOf_powDopOf_kernel hd

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
