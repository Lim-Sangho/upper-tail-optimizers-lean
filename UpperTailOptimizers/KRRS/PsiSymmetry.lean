import UpperTailOptimizers.KRRS.PsiNondeg

/-!
# Steps 1, 3 and 5 of Kenyon–Radin–Ren–Sadun, Theorem 3.3

`thm:krrs-cross-density` of `paper/bipodal_optimizer.tex` quotes Kenyon–Radin–Ren–Sadun
(arXiv:1509.05370) Theorem 3.3: for fixed `d` and `ε` the equation `∂_zψ_d(ε,z) = 0` has a
unique solution `ζ_d(ε)`, and `ζ_d` is a strictly decreasing involution fixing `(d-1)/d`.
Their proof runs in five steps; **Step 3** is the observation that makes `ζ_d` an involution:

> If `ND' = DN'`, then `N/D = N'/D'`. … Note that `N'` and `D'` are odd under interchange of
> `ε` and `ε̃`, so the second equation is invariant under this interchange.  Furthermore, we
> have `(ε̃-ε)N' - N` is the same as `N` with the roles of `ε` and `ε̃` reversed, while
> `(ε̃-ε)D' - D` is the same as `D` with the roles reversed.  Thus the two equations are
> satisfied for `(ε,ε̃)` if and only if they are satisfied for `(ε̃,ε)`.

That step is a chain of four algebraic identities, and this file proves them and the
symmetry they give.  With

  `Wr d ε z = 𝒩'_ε(z)𝒟_ε(z) - 𝒩_ε(z)𝒟'_ε(z)`

the numerator of `∂_zψ_d` (`KRRS/PsiNondeg.lean`), the conclusion is the unconditional
identity `Wr d z ε = Wr d ε z`.  Nothing about maximality, uniqueness or even the range of
`ε` and `z` is needed: it holds for all reals.

## What this gives, and what it does not

Combined with the uniqueness of the critical point — the part of Theorem 3.3 that is
assumed, since Kenyon–Radin–Ren–Sadun derive it by a continuity argument in a *real*
parameter `k` that their Step 4 sketches — the symmetry yields the involution property:
if `ζ_d(ε)` is the unique critical point of `ψ_d(ε,·)`, then `ε` is a critical point of
`ψ_d(ζ_d(ε),·)`, hence equals `ζ_d(ζ_d(ε))`.  `KRRS/Inputs.lean` performs that derivation,
so `involutive` is a theorem there rather than an assumption.

## Contents

* `dN_swap`, `Nfun_swap`, `dD_swap`, `Dfun_swap` — the four reversal identities: `𝒩'` and
  `𝒟'` are odd, and `𝒩`, `𝒟` reverse into `(z-ε)·(derivative) - (itself)`;
* `Wr_swap` — Step 3: `Wr d z ε = Wr d ε z`;
* `Wr_eq_zero_swap` — its use: a critical point relation is symmetric;
* `Wr_eq_zero_of_isMax` — an interior maximizer is a critical point (from
  `krrs_scalar_nondegenerate`);
* `sub_two_mul_pow_succ`, `diagonalTest_mul`, `diagonalTest_eq_zero_iff` — Step 1: the
  diagonal is a critical point of the filled-in `ψ_d(ε,·)` exactly at `ε = (d-1)/d`;
* `hasDerivAt_Wr_left` — the identity Step 5 turns on, `∂_ε Wr(ε,z) = dWr(z,ε)`.
-/

namespace UpperTailOptimizers

open Real

/-! ### The four reversal identities -/

/-- `𝒩'` is **odd** under interchanging `ε` and `z`. -/
theorem dN_swap (ε z : ℝ) : dN z ε = -dN ε z := by
  unfold dN; ring

/-- `𝒟'` is **odd** under interchanging `ε` and `z`. -/
theorem dD_swap (d : ℕ) (ε z : ℝ) : dD d z ε = -dD d ε z := by
  unfold dD; ring

/-- `𝒩` with the roles of `ε` and `z` reversed is `(z-ε)𝒩'_ε(z) - 𝒩_ε(z)`.

Both sides are `2[S₀(ε) - S₀(z) + S₀'(z)(z-ε)]`: the Taylor remainders of `S₀` based at the
two ends of the same interval are exchanged by this operation. -/
theorem Nfun_swap (ε z : ℝ) : Nfun z ε = (z - ε) * dN ε z - Nfun ε z := by
  rw [dN_eq_two_mul_dS0]
  unfold Nfun
  ring

/-- `𝒟` with the roles of `ε` and `z` reversed is `(z-ε)𝒟'_ε(z) - 𝒟_ε(z)`.

The same statement for `z ↦ z^d` in place of `S₀`; the powers `z^{d-1}` never have to be
recombined with `z`, so no hypothesis on `d` is needed. -/
theorem Dfun_swap (d : ℕ) (ε z : ℝ) : Dfun d z ε = (z - ε) * dD d ε z - Dfun d ε z := by
  unfold Dfun dD
  ring

/-! ### Step 3 -/

/-- **Step 3 of Kenyon–Radin–Ren–Sadun, Theorem 3.3.**  The numerator of `∂_zψ_d` is
*symmetric* in its two arguments:

  `Wr d z ε = Wr d ε z`.

Substituting the four reversal identities, the two cross terms `(z-ε)𝒩'𝒟'` cancel and what
is left is `𝒩'𝒟 - 𝒩𝒟'` again.  Holds for all real `ε`, `z` and all `d`. -/
theorem Wr_swap (d : ℕ) (ε z : ℝ) : Wr d z ε = Wr d ε z := by
  have h1 := dN_swap ε z
  have h2 := Nfun_swap ε z
  have h3 := dD_swap d ε z
  have h4 := Dfun_swap d ε z
  unfold Wr
  rw [h1, h2, h3, h4]
  ring

/-- **The critical-point relation is symmetric.**  If `z` is a critical point of
`ψ_d(ε,·)`, then `ε` is a critical point of `ψ_d(z,·)`. -/
theorem Wr_eq_zero_swap {d : ℕ} {ε z : ℝ} (h : Wr d ε z = 0) : Wr d z ε = 0 := by
  rw [Wr_swap]; exact h

/-- **An interior maximizer is a critical point.**  The first half of
`krrs_scalar_nondegenerate`, named for use with Step 3. -/
theorem Wr_eq_zero_of_isMax {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ}
    (hε0 : 0 < ε) (hz0 : 0 < z) (hz1 : z < 1) (hne : z ≠ ε) (hstar : z ≠ rStar d)
    (hmax : ∀ w, 0 < w → w < 1 → w ≠ ε → psiD d ε w ≤ psiD d ε z) :
    Wr d ε z = 0 :=
  (krrs_scalar_nondegenerate hd hε0 hz0 hz1 hne hstar hmax).1


/-! ## Step 1: the diagonal test

Near `z = ε` both `N` and `D` have a double root, so the quotient `ψ_d(ε,z)` equals
`(N'' + N'''(z-ε)/3 + …) / (D'' + D'''(z-ε)/3 + …)` with all derivatives taken at `ε`, and the
source's Step 1 reads off that `∂_zψ_d(ε,ε) = 0` — the diagonal being a critical point of the
filled-in `ψ_d` — is equivalent to `N''(ε)D'''(ε) = N'''(ε)D''(ε)`.  Their computation then
turns that into `dε = d-1`.  That is `diagonalTest_eq_zero_iff` below. -/

/-- `(d-2)ε^{d-3}·ε = (d-2)ε^{d-2}`, for every `d ≥ 2`.

The two exponents are **natural** subtractions, so `d = 2` has to be separated: there
`ε^{d-3} = ε^0 = 1` rather than `ε^{-1}`, and the identity survives only because the factor
`d - 2` vanishes. -/
theorem sub_two_mul_pow_succ {d : ℕ} (hd : 2 ≤ d) (ε : ℝ) :
    ((d : ℝ) - 2) * ε ^ (d - 3) * ε = ((d : ℝ) - 2) * ε ^ (d - 2) := by
  rcases eq_or_lt_of_le hd with h | h
  · have h2 : (d : ℝ) - 2 = 0 := by rw [← h]; norm_num
    rw [h2]; ring
  · have hpow : ε ^ (d - 3) * ε = ε ^ (d - 2) := by
      rw [← pow_succ]; congr 1; omega
    rw [mul_assoc, hpow]

/-- **The diagonal test, cleared of denominators.**

  `(N''(ε)D'''(ε) - N'''(ε)D''(ε))·ε²(1-ε)² = -d(d-1)ε^{d-2}·((d-1) - dε)`.

The bracket `(1-ε)(d-2) + (1-2ε)` collapses to `(d-1) - dε`, which is the source's
`kε = k-1`. -/
theorem diagonalTest_mul {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (d2N ε * d3D d ε - d3N ε * d2D d ε) * (ε ^ 2 * (1 - ε) ^ 2)
      = -((d : ℝ) * ((d : ℝ) - 1) * ε ^ (d - 2) * (((d : ℝ) - 1) - (d : ℝ) * ε)) := by
  have hεne : ε ≠ 0 := ne_of_gt h0
  have h1ne : (1 : ℝ) - ε ≠ 0 := by intro h; exact absurd h1 (by linarith)
  have hD3 : d3D d ε * ε = (d : ℝ) * ((d : ℝ) - 1) * (((d : ℝ) - 2) * ε ^ (d - 2)) := by
    have hk := sub_two_mul_pow_succ hd ε
    unfold d3D
    calc (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * ε ^ (d - 3) * ε
        = (d : ℝ) * ((d : ℝ) - 1) * (((d : ℝ) - 2) * ε ^ (d - 3) * ε) := by ring
      _ = (d : ℝ) * ((d : ℝ) - 1) * (((d : ℝ) - 2) * ε ^ (d - 2)) := by rw [hk]
  have e1 : d2N ε * (ε ^ 2 * (1 - ε) ^ 2) = -(ε * (1 - ε)) := by
    unfold d2N; field_simp
  have e2 : d3N ε * (ε ^ 2 * (1 - ε) ^ 2) = 1 - 2 * ε := by
    unfold d3N; field_simp
  calc (d2N ε * d3D d ε - d3N ε * d2D d ε) * (ε ^ 2 * (1 - ε) ^ 2)
      = (d2N ε * (ε ^ 2 * (1 - ε) ^ 2)) * d3D d ε
        - (d3N ε * (ε ^ 2 * (1 - ε) ^ 2)) * d2D d ε := by ring
    _ = -(ε * (1 - ε)) * d3D d ε - (1 - 2 * ε) * d2D d ε := by rw [e1, e2]
    _ = -((1 - ε) * (d3D d ε * ε)) - (1 - 2 * ε) * d2D d ε := by ring
    _ = -((d : ℝ) * ((d : ℝ) - 1) * ε ^ (d - 2) * (((d : ℝ) - 1) - (d : ℝ) * ε)) := by
        rw [hD3]; unfold d2D; ring

/-- **Step 1 of Kenyon–Radin–Ren–Sadun, Theorem 3.3.**  The diagonal is a critical point of the
filled-in `ψ_d(ε,·)` exactly at the exceptional density:

  `N''(ε)D'''(ε) = N'''(ε)D''(ε)  ↔  ε = (d-1)/d`. -/
theorem diagonalTest_eq_zero_iff {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    d2N ε * d3D d ε = d3N ε * d2D d ε ↔ ε = rStar d := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
  have hd1 : (1 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hεne : ε ≠ 0 := ne_of_gt h0
  have h1ne : (1 : ℝ) - ε ≠ 0 := by intro h; exact absurd h1 (by linarith)
  have hden : ε ^ 2 * (1 - ε) ^ 2 ≠ 0 := by positivity
  have hpow : (0 : ℝ) < ε ^ (d - 2) := pow_pos h0 _
  have hmul := diagonalTest_mul hd h0 h1
  rw [← sub_eq_zero]
  constructor
  · intro h
    rw [h, zero_mul] at hmul
    have hz : (d : ℝ) * ((d : ℝ) - 1) * ε ^ (d - 2) * (((d : ℝ) - 1) - (d : ℝ) * ε) = 0 := by
      linarith [hmul]
    have hfac : ((d : ℝ) - 1) - (d : ℝ) * ε = 0 := by
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' (by positivity)
      · exact h'
    rw [rStar]
    field_simp
    linarith
  · intro h
    have hfac : ((d : ℝ) - 1) - (d : ℝ) * ε = 0 := by
      have hmulε : (d : ℝ) * ε = (d : ℝ) - 1 := by
        rw [h, rStar]; field_simp
      linarith
    rw [hfac, mul_zero, neg_zero] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right hden


/-! ## Step 5: the two partial derivatives of the critical-point equation

The source's Step 5 differentiates `f(ε,z) = D N' - N D' = Wr` implicitly along the curve
`f = 0` to get `dζ/dε = -ḟ/f'`, and its whole content is the observation

> The arguments in the last line are written in the correct order!  That is, `ḟ` is the same
> as `f'`, only with the roles of `ε` and `ε̃` reversed.

With `Wr_swap` in hand that is immediate: `x ↦ Wr d x z` **is** `x ↦ Wr d z x`, so its
derivative at `ε` is `dWr d z ε`.  Their Step 2 then gives `f' ≠ 0` and, by this identity and
the symmetry of `f = 0`, also `ḟ ≠ 0`. -/

/-- **Step 5 of Kenyon–Radin–Ren–Sadun, Theorem 3.3**: the derivative of `Wr` in its *first*
argument is the derivative in its second with the roles of the arguments exchanged,

  `∂_ε Wr(ε,z) = dWr(z,ε)`.

Immediate from `Wr_swap`, which makes the two functions equal. -/
theorem hasDerivAt_Wr_left (d : ℕ) (z : ℝ) {ε : ℝ} (h0 : ε ≠ 0) (h1 : ε ≠ 1) :
    HasDerivAt (fun x => Wr d x z) (dWr d z ε) ε := by
  have h : (fun x => Wr d x z) = fun x => Wr d z x := funext fun x => Wr_swap d z x
  rw [h]
  exact hasDerivAt_Wr d z h0 h1

end UpperTailOptimizers
