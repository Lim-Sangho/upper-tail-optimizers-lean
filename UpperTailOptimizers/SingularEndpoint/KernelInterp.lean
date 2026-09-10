import UpperTailOptimizers.SingularEndpoint.PowInterp
import UpperTailOptimizers.SingularEndpoint.DistributionMeasure

/-!
# The exact two-variable kernel decomposition (Section 7, `paper/singular_endpoint.tex`)

The **exact algebraic half** of the interpolation decomposition in the proof of
`lem:central-kernel-bound`.  That proof expands
the law kernel

  `K_h(x,y) = J_{p_h}(xy)`

on the central square by interpolating in each variable separately in the basis `{1, x^d}` at
the two nodes `s_h, t_h`.  This file realises

* `eq:moment-interpolation` — the operators `I_h^x, R_h^x` (and their `y`-analogues), and the
  theorem `interpFst_eq_lagrange` identifying `I_h^x` with the paper's displayed Lagrange
  formula `((t^d - x^d)F(s,y) + (x^d - s^d)F(t,y))/(t^d - s^d)`;
* the exact four-term identity
  `K = I^xI^yK + R^xI^yK + I^xR^yK + R^xR^yK` (`interp_resid_decomposition`, the unlabelled identity
  opening the proof of `lem:central-kernel-bound`), together with the commutation of the two operators;
* the exact kernel decomposition — an unlabelled display in the same proof —
  `K_h = P_h + Q_h(x)(u_{0,h}(x) + u_{d,h}(x)y^d) + Q_h(y)(u_{0,h}(y) + u_{d,h}(y)x^d)
  + Q_h(x)Q_h(y)Θ_h(x,y)`,
  as `KKTFamily.kernel_decomposition`, with `P_h` exhibited as
  `p_{00} + p_{d0}x^d + p_{0d}y^d + p_{dd}x^dy^d` and `p_{d0} = p_{0d}`.

**Out of scope, deliberately.**  The value `Θ_0(u_*,u_*) = d^3/4` belongs to
`SingularEndpoint/KernelTheta.lean` and the corner-error clause `‖Θ_h - d³/4‖_∞ ≤ a/8` to `SingularEndpoint/KernelError.lean`, as does the uniform boundedness of `u_{0,h}`,
`u_{d,h}` and `Θ_h`; the four coefficients `p_{··,h}` are bounded in
`SingularEndpoint/PowFirstOrder.lean`.  See "What is not here" below.

## The route

Everything rests on `SingularEndpoint/PowInterp.lean`, which is the one-variable theory of exactly
this interpolation: the paper's `I_h^x` applied to a function `F` of two variables is, slice
by slice,

  `(I_h^xF)(x,y) = powCoefA d (F · y) s t + powCoefB d (F · y) s t · x^d`,
  `(R_h^xF)(x,y) = powResid d (F · y) s t x`,

with `s = B.sVal h`, `t = B.tVal h`.  Three ingredients then do all the work.

* **Linearity.**  `powCoefA`, `powCoefB`, `powResid` are linear in the function
  (`powCoefA_add_const_mul` and friends), and `powResid` annihilates the interpolation basis
  — this is what lets `R^x` be pushed
  through the affine-in-`y^d` expression `I^yK = A(x) + B(x)y^d`, and it is used through
  `powResid_const_mul` and `interp_resid_decomposition` rather than stated on its own.
* **The two `Q_h` factors.**  `powResid_eq_powDD_mul` (`SingularEndpoint/PowInterp.lean`) factors the
  residual as `(x^d - s^d)(x^d - t^d)·powDD`, and the geometric-sum factorisation
  `pow_sub_pow_eq` (`Nondegeneracy/PowBounds.lean`) turns `(x^d - s^d)(x^d - t^d)` into
  `Q_h(x)·mfac(x)` with `Q_h(x) = (x - s_h)(x - t_h)` (`KKTFamily.Qh`) and
  `mfac(x) = (∑_{i<d} x^i s_h^{d-1-i})(∑_{i<d} x^i t_h^{d-1-i})`.  No division is performed
  and nothing degenerates as the nodes coalesce.
* **Symmetry.**  `K_h(x,y) = J_{p_h}(xy)` is symmetric, so the two coefficient slices agree
  (`KKTFamily.kernelCoefA_slice`, `.kernelCoefB_slice`) and the `y`-analogue of the
  second term uses the *same* one-variable functions `u_{0,h}, u_{d,h}` — this is the paper's
  "the third term is the symmetric `y`-analogue" , and it halves the work.

The degree `d` is symbolic throughout; no degree count is performed anywhere.

## Nonnegativity of the arguments

`kernel_decomposition` carries `0 ≤ x` and `0 ≤ y`, which the paper does not display because
it works on `𝓝_ρ ⊂ (0,∞)` throughout.  The hypothesis is genuinely needed and is not a
weakening: the factorisation `powResid_eq_powDD_mul` runs through the chart `w = x^d`, whose
round trip `(x^d)^{1/d} = x` is false for `x < 0` and even `d`.

## What is not here

The uniform-boundedness clause of the proof of `lem:central-kernel-bound` — the now
`ρ`-uniform bound `max{|p_{ij,h}|, |u_{i,h}(x)|, |v_{i,h}(x)|, |Θ_h(x,y)|} ≤ C_d`
— is proved here **only for the
geometric cofactor**
(`mfac_mem_Icc`, `KKTFamily.exists_mfac_window`), which is the paper's own reason that
the algebraic quotients `(x^d - s_h^d)/(x - s_h)`, `(x^d - t_h^d)/(x - t_h)` "are uniformly
bounded above and away from zero on `I`".  The remaining factor of each bound is a divided
difference of
`K_h` — `powDD` of `kernelCoefA`, of `kernelCoefB`, and the iterated `powDD` of
`kernelTheta` — and bounding those through `powDD_mem_of_powDeriv2_mem` needs a derivative
chain for the coefficient slices together with uniform bounds on `J_{p_h}', J_{p_h}''` and
`J_{p_h}'''` near `r_*`, which is not attempted in this file.  The bounds it therefore leaves
out — those on `p_{00,h}, p_{d0,h}, p_{0d,h}, p_{dd,h}`, on `u_{0,h}, u_{d,h}` and on `Θ_h` —
are supplied later instead: the four coefficients of `P_h` in `SingularEndpoint/PowFirstOrder.lean`
(`exists_kp00_window`, `exists_kpd0_window`, `exists_kp0d_window`, `exists_kpdd_window`), and
the two one-variable functions and the corner quotient in `SingularEndpoint/KernelError.lean`
(`exists_u0_window`, `exists_ud_window`, `exists_kernelTheta_bound`, with the accuracy clause
`exists_kernelTheta_error`).  Nothing below is stated conditionally, and nothing is weakened:
every theorem in this file is an unconditional exact identity or an explicit two-sided bound.

## Contents

* `powCoefA_add_const_mul`, `powCoefB_add_const_mul`, `powResid_add_const_mul`,
  `powResid_const_mul` — linearity in the function;
* `interpFst`, `residFst`, `interpSnd`, `residSnd` — `eq:moment-interpolation`, with
  `interpFst_eq_lagrange`, `interpSnd_eq_lagrange` and the splittings
  `interpFst_add_residFst`, `interpSnd_add_residSnd`;
* `interp_resid_decomposition` — the four-term identity;
* `interpFst_interpSnd_comm`, `interpFst_residSnd_comm` — the commutation of the two
  interpolation operators;
* `powGeom`, `mfac`, `pow_sub_pow_mul_eq`, `powResid_eq_mfac_mul` — the extraction of the
  `Q_h` factor, and `powGeom_mem_Icc`, `mfac_mem_Icc` for the explicit two-sided bounds;
* `KKTFamily.kernel`, `.kernelCoefA`, `.kernelCoefB` — the law kernel and the two
  coefficient slices of `I_h^yK_h`, with the symmetry lemmas;
* `KKTFamily.kp00`, `.kpd0`, `.kp0d`, `.kpdd`, `.kernelPoly` — the paper's `P_h`, with the
  symmetry `kpd0_eq_kp0d`;
* `KKTFamily.u0`, `.ud`, `.kernelTheta` — the one-variable functions `u_{0,h}, u_{d,h}`
  and the corner quotient `Θ_h`;
* `KKTFamily.interpFst_interpSnd_kernel`, `.residFst_interpSnd_kernel`,
  `.interpFst_residSnd_kernel`, `.residFst_residSnd_kernel` — the four terms;
* `KKTFamily.kernel_decomposition` — **the kernel decomposition** as an exact identity;
* `KKTFamily.exists_mfac_window` — the geometric cofactor is bounded above and away from
  zero on the central window, uniformly in small `h`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

/-! ## Linearity of the one-variable interpolation in the function

`powCoefA`, `powCoefB` and `powResid` (`SingularEndpoint/PowInterp.lean`) are linear in `φ`.  No
hypothesis is needed: when the nodes collide in the `w`-coordinate the common denominator
`t^d - s^d` is zero and all three sides are zero by Lean's `x / 0 = 0`. -/

/-- The `x^d` coefficient is linear in the function. -/
theorem powCoefB_add_const_mul (d : ℕ) (phi psi : ℝ → ℝ) (c s t : ℝ) :
    powCoefB d (fun z => phi z + c * psi z) s t
      = powCoefB d phi s t + c * powCoefB d psi s t := by
  simp only [powCoefB]
  ring

/-- The constant coefficient is linear in the function. -/
theorem powCoefA_add_const_mul (d : ℕ) (phi psi : ℝ → ℝ) (c s t : ℝ) :
    powCoefA d (fun z => phi z + c * psi z) s t
      = powCoefA d phi s t + c * powCoefA d psi s t := by
  simp only [powCoefA, powCoefB]
  ring

/-- **The residual is linear in the function.**  This is what makes the two-variable
bookkeeping of the four-term interpolation identity work: `R_h^x` may be pushed through
the affine-in-`y^d` expression `I_h^yK_h = A(x) + B(x)y^d`, the scalar `c` being `y^d`. -/
theorem powResid_add_const_mul (d : ℕ) (phi psi : ℝ → ℝ) (c s t x : ℝ) :
    powResid d (fun z => phi z + c * psi z) s t x
      = powResid d phi s t x + c * powResid d psi s t x := by
  simp only [powResid, powCoefA, powCoefB]
  ring

/-- Homogeneity of the residual, used to pull the constant `Q_h(y)·mfac(y)` out of the
fourth term of the decomposition. -/
theorem powResid_const_mul (d : ℕ) (c : ℝ) (psi : ℝ → ℝ) (s t x : ℝ) :
    powResid d (fun z => c * psi z) s t x = c * powResid d psi s t x := by
  simp only [powResid, powCoefA, powCoefB]
  ring

/-! ## The two-variable operators `I_h^x, R_h^x, I_h^y, R_h^y`

`eq:moment-interpolation`.  The operators are defined as maps on functions of two variables
so that they can be composed, which is what the four-term identity opening the proof of
`lem:central-kernel-bound` requires. -/

/-- **The interpolation operator `I_h^x` in the first variable** of
`eq:moment-interpolation`, written in the coefficient form `A + Bx^d` of
`SingularEndpoint/PowInterp.lean`.  `interpFst_eq_lagrange` is the identification with the paper's
displayed Lagrange formula. -/
noncomputable def interpFst (d : ℕ) (s t : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x y => powCoefA d (fun z => F z y) s t + powCoefB d (fun z => F z y) s t * x ^ d

/-- **The residual operator `R_h^x = Id - I_h^x` in the first variable** of
`eq:moment-interpolation`. -/
noncomputable def residFst (d : ℕ) (s t : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x y => powResid d (fun z => F z y) s t x

/-- **The interpolation operator `I_h^y` in the second variable**, defined analogously. -/
noncomputable def interpSnd (d : ℕ) (s t : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x y => powCoefA d (fun z => F x z) s t + powCoefB d (fun z => F x z) s t * y ^ d

/-- **The residual operator `R_h^y = Id - I_h^y` in the second variable.** -/
noncomputable def residSnd (d : ℕ) (s t : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x y => powResid d (fun z => F x z) s t y

/-- **The correspondence with `eq:moment-interpolation` as the paper displays it.**  For
separated nodes,

  `(I_h^xF)(x,y) = (t^d - x^d)/(t^d - s^d)·F(s,y) + (x^d - s^d)/(t^d - s^d)·F(t,y)`.

The coefficient form of `interpFst` is the same expression collected in the basis
`{1, x^d}`. -/
theorem interpFst_eq_lagrange {d : ℕ} {s t : ℝ} (hD : t ^ d - s ^ d ≠ 0) (F : ℝ → ℝ → ℝ)
    (x y : ℝ) :
    interpFst d s t F x y
      = (t ^ d - x ^ d) / (t ^ d - s ^ d) * F s y
        + (x ^ d - s ^ d) / (t ^ d - s ^ d) * F t y := by
  simp only [interpFst, powCoefA, powCoefB]
  field_simp
  ring

/-- The second-variable form of `eq:moment-interpolation`, the analogue of
`interpFst_eq_lagrange`. -/
theorem interpSnd_eq_lagrange {d : ℕ} {s t : ℝ} (hD : t ^ d - s ^ d ≠ 0) (F : ℝ → ℝ → ℝ)
    (x y : ℝ) :
    interpSnd d s t F x y
      = (t ^ d - y ^ d) / (t ^ d - s ^ d) * F x s
        + (y ^ d - s ^ d) / (t ^ d - s ^ d) * F x t := by
  simp only [interpSnd, powCoefA, powCoefB]
  field_simp
  ring

/-- `Id = I_h^x + R_h^x` in the first variable; this is the definition of `powResid`. -/
theorem interpFst_add_residFst (d : ℕ) (s t : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    interpFst d s t F x y + residFst d s t F x y = F x y := by
  simp only [interpFst, residFst, powResid]
  ring

/-- `Id = I_h^y + R_h^y` in the second variable. -/
theorem interpSnd_add_residSnd (d : ℕ) (s t : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    interpSnd d s t F x y + residSnd d s t F x y = F x y := by
  simp only [interpSnd, residSnd, powResid]
  ring

/-- **The exact four-term identity**

  `F = I^xI^yF + R^xI^yF + I^xR^yF + R^xR^yF`,

stated pointwise.  It carries **no hypothesis whatsoever** — not even node separation — being
two applications of `Id = I + R`, first in the second variable and then in the first.  No
analysis is involved. -/
theorem interp_resid_decomposition (d : ℕ) (s t : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    F x y
      = interpFst d s t (interpSnd d s t F) x y
        + residFst d s t (interpSnd d s t F) x y
        + interpFst d s t (residSnd d s t F) x y
        + residFst d s t (residSnd d s t F) x y := by
  have h1 := interpFst_add_residFst d s t (interpSnd d s t F) x y
  have h2 := interpFst_add_residFst d s t (residSnd d s t F) x y
  have h3 := interpSnd_add_residSnd d s t F x y
  linarith

/-! ## The two operators commute

Unfolding both sides expresses each as one rational expression in the four node values
`F(s,s), F(s,t), F(t,s), F(t,t)` and the powers `s^d, t^d, x^d, y^d`; the identity is then
pure algebra.  Equivalently, it is the four "Fubini" identities relating the coefficients
extracted in the two orders. -/

/-- **The two interpolation operators commute**, the symmetry the four-term decomposition of
`lem:central-kernel-bound` relies on.  No hypothesis is needed. -/
theorem interpFst_interpSnd_comm (d : ℕ) (s t : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    interpFst d s t (interpSnd d s t F) x y = interpSnd d s t (interpFst d s t F) x y := by
  simp only [interpFst, interpSnd, powCoefA, powCoefB]
  ring

/-- **`I_h^x` commutes with `R_h^y`.**  This is the form of the commutation the decomposition
actually consumes: it converts the third term `I^xR^yK` into `R^y(I^xK)`, whose `y`-residual
carries the factor `Q_h(y)`. -/
theorem interpFst_residSnd_comm (d : ℕ) (s t : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    interpFst d s t (residSnd d s t F) x y = residSnd d s t (interpFst d s t F) x y := by
  simp only [interpFst, residSnd, powResid, powCoefA, powCoefB]
  ring

/-! ## Extracting the `Q_h` factor from the residual

`powResid_eq_powDD_mul` writes the residual as `(x^d - s^d)(x^d - t^d)·powDD`; the
geometric-sum factorisation `pow_sub_pow_eq` (`Nondegeneracy/PowBounds.lean`) then splits off
the node quadratic `(x - s)(x - t)`, which for the family nodes is `KKTFamily.Qh`. -/

/-- **The geometric cofactor** `∑_{i<d} x^i s^{d-1-i}` of `x^d - s^d = (x - s)·powGeom`.  It
is the quotient behind the paper's remark, in the proof of `lem:central-kernel-bound`,
that although the individual coefficients of `eq:moment-interpolation` contain
`(t_h^d - s_h^d)^{-1}`, the combined interpolants and remainders have convergent limits. -/
noncomputable def powGeom (d : ℕ) (x s : ℝ) : ℝ := ∑ i ∈ Finset.range d, x ^ i * s ^ (d - 1 - i)

/-- **The product of the two geometric cofactors**,
`mfac d s t x = powGeom d x s · powGeom d x t`, so that
`(x^d - s^d)(x^d - t^d) = (x - s)(x - t)·mfac d s t x`. -/
noncomputable def mfac (d : ℕ) (s t x : ℝ) : ℝ := powGeom d x s * powGeom d x t

/-- The node product in the `w`-coordinate, factored through the node quadratic: it is the
geometric-sum factorisation applied in each factor. -/
theorem pow_sub_pow_mul_eq (d : ℕ) (s t x : ℝ) :
    (x ^ d - s ^ d) * (x ^ d - t ^ d) = (x - s) * (x - t) * mfac d s t x := by
  rw [pow_sub_pow_eq x s d, pow_sub_pow_eq x t d, mfac, powGeom, powGeom]
  ring

/-- **The residual carries the node quadratic as a factor.**  For `0 ≤ s < t` and `0 ≤ x`,

  `powResid d φ s t x = (x - s)(x - t)·(mfac d s t x · powDD d φ s t x)`.

This is `powResid_eq_powDD_mul` (`SingularEndpoint/PowInterp.lean`) followed by
`pow_sub_pow_mul_eq`.  No division is performed, so nothing degenerates as `t - s ↓ 0`. -/
theorem powResid_eq_mfac_mul {d : ℕ} (hd : d ≠ 0) (phi : ℝ → ℝ) {s t x : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hst : s < t) :
    powResid d phi s t x = (x - s) * (x - t) * (mfac d s t x * powDD d phi s t x) := by
  rw [powResid_eq_powDD_mul hd phi hs ht hx hst, pow_sub_pow_mul_eq]
  ring

/-- **The geometric cofactor is bounded above and away from zero**, with explicit constants:
on `m ≤ x, s ≤ M` with `0 < m` each of the `d` summands `x^i s^{d-1-i}` lies between
`m^{d-1}` and `M^{d-1}`, so `d·m^{d-1} ≤ powGeom d x s ≤ d·M^{d-1}`.  The degree is symbolic
and no compactness argument is used. -/
theorem powGeom_mem_Icc {d : ℕ} {m M x s : ℝ} (hm : 0 < m) (hx : x ∈ Set.Icc m M)
    (hs : s ∈ Set.Icc m M) :
    (d : ℝ) * m ^ (d - 1) ≤ powGeom d x s ∧ powGeom d x s ≤ (d : ℝ) * M ^ (d - 1) := by
  have hx0 : 0 ≤ x := hm.le.trans hx.1
  have hs0 : 0 ≤ s := hm.le.trans hs.1
  have hcard : ∀ c : ℝ, ∑ _i ∈ Finset.range d, c = (d : ℝ) * c := by
    intro c
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  constructor
  · rw [powGeom, ← hcard (m ^ (d - 1))]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i + (d - 1 - i) = d - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hsplit : m ^ (d - 1) = m ^ i * m ^ (d - 1 - i) := by rw [← pow_add, hi']
    rw [hsplit]
    exact mul_le_mul (pow_le_pow_left₀ hm.le hx.1 i) (pow_le_pow_left₀ hm.le hs.1 _)
      (pow_nonneg hm.le _) (pow_nonneg hx0 i)
  · rw [powGeom, ← hcard (M ^ (d - 1))]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i + (d - 1 - i) = d - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hsplit : M ^ (d - 1) = M ^ i * M ^ (d - 1 - i) := by rw [← pow_add, hi']
    rw [hsplit]
    exact mul_le_mul (pow_le_pow_left₀ hx0 hx.2 i) (pow_le_pow_left₀ hs0 hs.2 _)
      (pow_nonneg hs0 _) (pow_nonneg (hm.le.trans (hx.1.trans hx.2)) i)

/-- **The two-sided bound on `mfac`**, the square of `powGeom_mem_Icc`:

  `d²m^{2d-2} ≤ mfac d s t x ≤ d²M^{2d-2}`   for `x, s, t ∈ [m, M]`, `0 < m`.

This is the one uniform bound of the coefficient-bound clause of
`lem:central-kernel-bound` proved in this file; see the module docstring for where
the rest of that clause is proved. -/
theorem mfac_mem_Icc {d : ℕ} {m M x s t : ℝ} (hm : 0 < m) (hx : x ∈ Set.Icc m M)
    (hs : s ∈ Set.Icc m M) (ht : t ∈ Set.Icc m M) :
    (d : ℝ) ^ 2 * m ^ (2 * d - 2) ≤ mfac d s t x
      ∧ mfac d s t x ≤ (d : ℝ) ^ 2 * M ^ (2 * d - 2) := by
  obtain ⟨hsl, hsu⟩ := powGeom_mem_Icc (d := d) hm hx hs
  obtain ⟨htl, htu⟩ := powGeom_mem_Icc (d := d) hm hx ht
  have hexp : 2 * d - 2 = (d - 1) + (d - 1) := by omega
  have hml : (0 : ℝ) ≤ (d : ℝ) * m ^ (d - 1) := by positivity
  constructor
  · have : (d : ℝ) * m ^ (d - 1) * ((d : ℝ) * m ^ (d - 1)) ≤ powGeom d x s * powGeom d x t :=
      mul_le_mul hsl htl hml (le_trans hml hsl)
    rw [mfac, hexp, pow_add]
    linarith [this]
  · have hsn : (0 : ℝ) ≤ powGeom d x t := le_trans hml htl
    have : powGeom d x s * powGeom d x t ≤ (d : ℝ) * M ^ (d - 1) * ((d : ℝ) * M ^ (d - 1)) :=
      mul_le_mul hsu htu hsn (le_trans (le_trans hml hsl) hsu)
    rw [mfac, hexp, pow_add]
    linarith [this]

namespace KKTFamily

variable {d : ℕ}

/-! ## The law kernel and its coefficient slices -/

/-- **The law kernel** `K_h(x,y) = J_{p_h}(xy)` of `sec:auxiliary-lagrangian`,
the object the interpolation step of `lem:central-kernel-bound` expands. -/
noncomputable def kernel (B : KKTFamily d) (h x y : ℝ) : ℝ := Jp (B.p h) (x * y)

/-- The kernel is symmetric, since `xy = yx`.  This is what makes the third term of
the four-term identity "the symmetric `y`-analogue"  of the
second, with the *same* one-variable functions. -/
theorem kernel_symm (B : KKTFamily d) (h x y : ℝ) : B.kernel h x y = B.kernel h y x := by
  rw [kernel, kernel, mul_comm]

/-- **The constant coefficient of `I_h^yK_h`**, as a function of the frozen first variable:
`A_h(x) = powCoefA d (K_h(x,·)) s_h t_h`. -/
noncomputable def kernelCoefA (B : KKTFamily d) (h x : ℝ) : ℝ :=
  powCoefA d (fun z => B.kernel h x z) (B.sVal h) (B.tVal h)

/-- **The `y^d` coefficient of `I_h^yK_h`**, as a function of the frozen first variable:
`B_h(x) = powCoefB d (K_h(x,·)) s_h t_h`. -/
noncomputable def kernelCoefB (B : KKTFamily d) (h x : ℝ) : ℝ :=
  powCoefB d (fun z => B.kernel h x z) (B.sVal h) (B.tVal h)

/-- Freezing the *second* variable gives the same constant coefficient, by symmetry of the
kernel. -/
theorem kernelCoefA_slice (B : KKTFamily d) (h w : ℝ) :
    powCoefA d (fun z => B.kernel h z w) (B.sVal h) (B.tVal h) = B.kernelCoefA h w := by
  rw [kernelCoefA]
  congr 1
  funext z
  exact kernel_symm B h z w

/-- Freezing the *second* variable gives the same `x^d` coefficient, by symmetry of the
kernel. -/
theorem kernelCoefB_slice (B : KKTFamily d) (h w : ℝ) :
    powCoefB d (fun z => B.kernel h z w) (B.sVal h) (B.tVal h) = B.kernelCoefB h w := by
  rw [kernelCoefB]
  congr 1
  funext z
  exact kernel_symm B h z w

/-- `I_h^yK_h` in coefficient form: `(I_h^yK_h)(x,y) = A_h(x) + y^d B_h(x)`. -/
theorem interpSnd_kernel_apply (B : KKTFamily d) (h x y : ℝ) :
    interpSnd d (B.sVal h) (B.tVal h) (B.kernel h) x y
      = B.kernelCoefA h x + y ^ d * B.kernelCoefB h x := by
  simp only [interpSnd, kernelCoefA, kernelCoefB]
  ring

/-- `I_h^xK_h` in coefficient form: `(I_h^xK_h)(x,y) = A_h(y) + x^d B_h(y)`.  The same two
functions occur, by symmetry of the kernel. -/
theorem interpFst_kernel_apply (B : KKTFamily d) (h x y : ℝ) :
    interpFst d (B.sVal h) (B.tVal h) (B.kernel h) x y
      = B.kernelCoefA h y + x ^ d * B.kernelCoefB h y := by
  rw [interpFst, kernelCoefA_slice, kernelCoefB_slice]
  ring

/-! ## The polynomial part `P_h` -/

/-- The constant coefficient `p_{00,h}` of `P_h`. -/
noncomputable def kp00 (B : KKTFamily d) (h : ℝ) : ℝ :=
  powCoefA d (B.kernelCoefA h) (B.sVal h) (B.tVal h)

/-- The coefficient `p_{d0,h}` of `x^d` in `P_h`. -/
noncomputable def kpd0 (B : KKTFamily d) (h : ℝ) : ℝ :=
  powCoefB d (B.kernelCoefA h) (B.sVal h) (B.tVal h)

/-- The coefficient `p_{0d,h}` of `y^d` in `P_h`. -/
noncomputable def kp0d (B : KKTFamily d) (h : ℝ) : ℝ :=
  powCoefA d (B.kernelCoefB h) (B.sVal h) (B.tVal h)

/-- The coefficient `p_{dd,h}` of `x^dy^d` in `P_h`. -/
noncomputable def kpdd (B : KKTFamily d) (h : ℝ) : ℝ :=
  powCoefB d (B.kernelCoefB h) (B.sVal h) (B.tVal h)

/-- **The polynomial part `P_h`** of the kernel decomposition,

  `P_h(x,y) = p_{00,h} + p_{d0,h}x^d + p_{0d,h}y^d + p_{dd,h}x^dy^d`,

the first term of the four-term identity, which lies in
`span{1,x^d} ⊗ span{1,y^d}`. -/
noncomputable def kernelPoly (B : KKTFamily d) (h x y : ℝ) : ℝ :=
  B.kp00 h + B.kpd0 h * x ^ d + B.kp0d h * y ^ d + B.kpdd h * (x ^ d * y ^ d)

/-- **`p_{d0,h} = p_{0d,h}`**: the polynomial part is symmetric, because the kernel is. -/
theorem kpd0_eq_kp0d (B : KKTFamily d) (h : ℝ) : B.kpd0 h = B.kp0d h := by
  have hsym : Jp (B.p h) (B.tVal h * B.sVal h) = Jp (B.p h) (B.sVal h * B.tVal h) := by
    rw [mul_comm]
  simp only [kpd0, kp0d, kernelCoefA, kernelCoefB, kernel, powCoefA, powCoefB, hsym]
  ring

/-! ## The one-variable functions `u_{0,h}, u_{d,h}` and the corner quotient `Θ_h` -/

/-- **The one-variable function `u_{0,h}`** of the kernel decomposition: the residual
of the constant coefficient `A_h`, divided by `Q_h`.  The division is performed once and for
all by `powResid_eq_mfac_mul`, so `u_{0,h}` is a *product*, not a quotient, and nothing
degenerates as the nodes coalesce. -/
noncomputable def u0 (B : KKTFamily d) (h x : ℝ) : ℝ :=
  mfac d (B.sVal h) (B.tVal h) x * powDD d (B.kernelCoefA h) (B.sVal h) (B.tVal h) x

/-- **The one-variable function `u_{d,h}`** of the kernel decomposition: the same
construction applied to the `y^d` coefficient `B_h`. -/
noncomputable def ud (B : KKTFamily d) (h x : ℝ) : ℝ :=
  mfac d (B.sVal h) (B.tVal h) x * powDD d (B.kernelCoefB h) (B.sVal h) (B.tVal h) x

/-- **The corner quotient `Θ_h`** of the kernel decomposition: the fourth term of
the four-term identity divided by `Q_h(x)Q_h(y)`, again realised as a
product of the two geometric cofactors with an iterated `powDD` — the divided difference in
`x` of the divided difference in `y`.  It is `Θ_h` that the deferred corner-error clause of
`lem:central-kernel-bound` compares with `d³/4`. -/
noncomputable def kernelTheta (B : KKTFamily d) (h x y : ℝ) : ℝ :=
  mfac d (B.sVal h) (B.tVal h) x * mfac d (B.sVal h) (B.tVal h) y
    * powDD d (fun z => powDD d (fun w => B.kernel h z w) (B.sVal h) (B.tVal h) y)
        (B.sVal h) (B.tVal h) x

/-! ## The four terms -/

/-- **The first term is `P_h`** : `I_h^xI_h^yK_h` lies in
`span{1,x^d} ⊗ span{1,y^d}`, and its four coefficients are `kp00, kpd0, kp0d, kpdd` by
linearity of the coefficient extraction. -/
theorem interpFst_interpSnd_kernel (B : KKTFamily d) (h x y : ℝ) :
    interpFst d (B.sVal h) (B.tVal h) (interpSnd d (B.sVal h) (B.tVal h) (B.kernel h)) x y
      = B.kernelPoly h x y := by
  have hfun : (fun z => interpSnd d (B.sVal h) (B.tVal h) (B.kernel h) z y)
      = fun z => B.kernelCoefA h z + y ^ d * B.kernelCoefB h z := by
    funext z
    exact interpSnd_kernel_apply B h z y
  simp only [interpFst]
  rw [hfun, powCoefA_add_const_mul, powCoefB_add_const_mul]
  simp only [kernelPoly, kp00, kpd0, kp0d, kpdd]
  ring

/-- **The second term is `Q_h(x){u_{0,h}(x) + u_{d,h}(x)y^d}`** : `R_h^x` is
pushed through the affine-in-`y^d` expression `I_h^yK_h = A_h + y^dB_h` by linearity, and
each of the two residuals carries the node quadratic `Q_h(x)` by
`powResid_eq_mfac_mul`. -/
theorem residFst_interpSnd_kernel (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) (hpos : 0 < h) {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    residFst d (B.sVal h) (B.tVal h) (interpSnd d (B.sVal h) (B.tVal h) (B.kernel h)) x y
      = B.Qh h x * (B.u0 h x + B.ud h x * y ^ d) := by
  have hd0 : d ≠ 0 := by omega
  have hs : (0 : ℝ) ≤ B.sVal h := (sVal_pos hh).le
  have ht : (0 : ℝ) ≤ B.tVal h := (tVal_pos hh).le
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  have hfun : (fun z => interpSnd d (B.sVal h) (B.tVal h) (B.kernel h) z y)
      = fun z => B.kernelCoefA h z + y ^ d * B.kernelCoefB h z := by
    funext z
    exact interpSnd_kernel_apply B h z y
  simp only [residFst]
  rw [hfun, powResid_add_const_mul, powResid_eq_mfac_mul hd0 _ hs ht hx hst,
    powResid_eq_mfac_mul hd0 _ hs ht hx hst]
  simp only [Qh, u0, ud]
  ring

/-- **The third term is the symmetric `y`-analogue** :
`Q_h(y){u_{0,h}(y) + u_{d,h}(y)x^d}`, with the *same* one-variable functions.  The commutation
`interpFst_residSnd_comm` turns `I^xR^yK_h` into `R^y(I^xK_h)`, and `interpFst_kernel_apply`
— which is where the symmetry `K_h(x,y) = K_h(y,x)` enters — identifies the coefficients of
`I^xK_h` with `A_h, B_h` again. -/
theorem interpFst_residSnd_kernel (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) (hpos : 0 < h) (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    interpFst d (B.sVal h) (B.tVal h) (residSnd d (B.sVal h) (B.tVal h) (B.kernel h)) x y
      = B.Qh h y * (B.u0 h y + B.ud h y * x ^ d) := by
  have hd0 : d ≠ 0 := by omega
  have hs : (0 : ℝ) ≤ B.sVal h := (sVal_pos hh).le
  have ht : (0 : ℝ) ≤ B.tVal h := (tVal_pos hh).le
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  have hfun : (fun w => interpFst d (B.sVal h) (B.tVal h) (B.kernel h) x w)
      = fun w => B.kernelCoefA h w + x ^ d * B.kernelCoefB h w := by
    funext w
    exact interpFst_kernel_apply B h x w
  rw [interpFst_residSnd_comm]
  simp only [residSnd]
  rw [hfun, powResid_add_const_mul, powResid_eq_mfac_mul hd0 _ hs ht hy hst,
    powResid_eq_mfac_mul hd0 _ hs ht hy hst]
  simp only [Qh, u0, ud]
  ring

/-- **The fourth term is `Q_h(x)Q_h(y)Θ_h(x,y)`** : the inner residual carries
`Q_h(y)` for every frozen first argument, so it factors out of the outer residual by
homogeneity, and the outer residual then carries `Q_h(x)`. -/
theorem residFst_residSnd_kernel (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ}
    (hh : |h| < B.h₀) (hpos : 0 < h) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    residFst d (B.sVal h) (B.tVal h) (residSnd d (B.sVal h) (B.tVal h) (B.kernel h)) x y
      = B.Qh h x * B.Qh h y * B.kernelTheta h x y := by
  have hd0 : d ≠ 0 := by omega
  have hs : (0 : ℝ) ≤ B.sVal h := (sVal_pos hh).le
  have ht : (0 : ℝ) ≤ B.tVal h := (tVal_pos hh).le
  have hst : B.sVal h < B.tVal h := B.sVal_lt_tVal hpos
  have hfun : (fun z => residSnd d (B.sVal h) (B.tVal h) (B.kernel h) z y)
      = fun z => ((y - B.sVal h) * (y - B.tVal h) * mfac d (B.sVal h) (B.tVal h) y)
          * powDD d (fun w => B.kernel h z w) (B.sVal h) (B.tVal h) y := by
    funext z
    simp only [residSnd]
    rw [powResid_eq_mfac_mul hd0 _ hs ht hy hst]
    ring
  simp only [residFst]
  rw [hfun, powResid_const_mul, powResid_eq_mfac_mul hd0 _ hs ht hx hst]
  simp only [Qh, kernelTheta]
  ring

/-! ## The exact identity -/

/-- **The kernel decomposition as an exact identity** — the target of this file: the unlabelled
display in the proof of `lem:central-kernel-bound`.
For `0 < h` inside the family window and `0 ≤ x, y`,

  `J_{p_h}(xy) = P_h(x,y) + Q_h(x){u_{0,h}(x) + u_{d,h}(x)y^d}
                          + Q_h(y){u_{0,h}(y) + u_{d,h}(y)x^d}
                          + Q_h(x)Q_h(y)Θ_h(x,y)`,

with `P_h(x,y) = p_{00,h} + p_{d0,h}x^d + p_{0d,h}y^d + p_{dd,h}x^dy^d` (`kernelPoly`) and
`p_{d0,h} = p_{0d,h}` (`kpd0_eq_kp0d`).

It is the four-term identity with the four terms evaluated.  No analysis
whatsoever is involved: every step is an algebraic identity between the values of `J_{p_h}` at
`s_h², s_ht_h, t_h²` and the powers `x^d, y^d, s_h^d, t_h^d`.  The uniform bounds on the
coefficients and on `Θ_h`, and the constant `Θ_0(u_*,u_*) = d³/4`, are **not** part of this
statement; see the module docstring. -/
theorem kernel_decomposition (hd : 2 ≤ d) (B : KKTFamily d) {h : ℝ} (hh : |h| < B.h₀)
    (hpos : 0 < h) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Jp (B.p h) (x * y)
      = B.kernelPoly h x y
        + B.Qh h x * (B.u0 h x + B.ud h x * y ^ d)
        + B.Qh h y * (B.u0 h y + B.ud h y * x ^ d)
        + B.Qh h x * B.Qh h y * B.kernelTheta h x y := by
  have hdec := interp_resid_decomposition d (B.sVal h) (B.tVal h) (B.kernel h) x y
  rw [interpFst_interpSnd_kernel B h x y, residFst_interpSnd_kernel hd B hh hpos hx y,
    interpFst_residSnd_kernel hd B hh hpos x hy,
    residFst_residSnd_kernel hd B hh hpos hx hy] at hdec
  exact hdec

/-! ## The one uniform bound proved here -/

/-- **The geometric cofactor is bounded above and away from zero on the central window,
uniformly in small `h`.**  For `0 < ρ ≤ u_*/2` there is a threshold `δ > 0` such that, for
every `0 < h < δ` and every `x ∈ 𝓝_ρ`,

  `d²(u_*/2)^{2d-2} ≤ mfac d s_h t_h x ≤ d²(3u_*/2)^{2d-2}`.

This is the quantitative form of the paper's remark, in the proof of
`lem:central-kernel-bound`, that the interpolants and remainders converge as the nodes
coalesce — here with explicit constants; the threshold `δ` comes from
`exists_atoms_mem_centralWindow`, which puts both nodes inside the window.

The remaining factors of the coefficient bounds of `lem:central-kernel-bound` — the
divided differences `powDD` occurring in `u0`, `ud`, `kernelTheta` and in the four
coefficients of `kernelPoly` — are **not** bounded in this file; see the module docstring. -/
theorem exists_mfac_window (hd : 2 ≤ d) (B : KKTFamily d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρu : ρ ≤ uStar d / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ x ∈ centralWindow d ρ,
      (d : ℝ) ^ 2 * (uStar d / 2) ^ (2 * d - 2) ≤ mfac d (B.sVal h) (B.tVal h) x
        ∧ mfac d (B.sVal h) (B.tVal h) x
            ≤ (d : ℝ) ^ 2 * (3 * uStar d / 2) ^ (2 * d - 2) := by
  obtain ⟨δ, hδ, hatoms⟩ := exists_atoms_mem_centralWindow B hρ
  have hu : 0 < uStar d := uStar_pos hd
  have hsub : ∀ z ∈ centralWindow d ρ, z ∈ Set.Icc (uStar d / 2) (3 * uStar d / 2) := by
    intro z hz
    simp only [centralWindow, Set.mem_Icc] at hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  refine ⟨δ, hδ, ?_⟩
  intro h hh0 hhδ x hxmem
  obtain ⟨hsmem, htmem⟩ := hatoms h hh0 hhδ
  exact mfac_mem_Icc (by linarith) (hsub x hxmem) (hsub _ hsmem) (hsub _ htmem)

end KKTFamily

end SingularEndpoint

end UpperTailOptimizers
