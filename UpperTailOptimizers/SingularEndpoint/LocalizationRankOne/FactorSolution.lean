import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.Factor
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorContraction
import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorLpBridge

/-!
# What follows from the nonlinear Factor equation (Section 5)

`lem:localization-rank-one` of `paper/sections/singular.tex` produces a nonnegative factor `f`
solving the nonlinear Factor equation `T_W(f^{d-1}) = qf` with `q = ∫f^d`.  The *production* of
`f` is a fixed-point argument (`SingularEndpoint/LocalizationRankOne/FactorContraction.lean` + `SingularEndpoint/LocalizationRankOne/FactorLpBridge.lean`).
This file proves everything the lemma asserts **downstream of the equation**: the solution `f`
is taken as a hypothesis throughout, and no fixed point is constructed here.

Written out, the standing hypothesis list is

`f` measurable, `0 ≤ f x` and `f x ≤ M` for every `x` (`M = contractionM d = 2/r_*`), `0 < q`,
`T_W(f^{d-1})(x) = q f(x)` for every `x`, and `q = ∫ f^d`.

## Paper results realised

* the pointwise half of `eq:rank-one-orthogonality` — the chain
  `q f(x) = ∫W(x,y)f(y)^{d-1}dy ≤ ∫f^{d-1} ≤ q^{(d-1)/d}` (in the paper an unlabelled
  display in the proof of `lem:localization-rank-one`),
  hence `f(x) ≤ q^{-1/d}`:
  `factorSolution_pointwise_bound`.  Both inequalities are proved, the
  second (`Hölder/Jensen`) in the division-free form `q^{1/d}·∫f^{d-1} ≤ q`
  (`factorSolution_rpow_mul_integral_le`), from the scalar AM–GM
  `n t a^{n-1} ≤ (n-1)a^n + t^n` (`factorSolution_amgm`, Bernoulli rescaled).
* the **orthogonality half of `eq:rank-one-orthogonality`**,
  `∫E(x,y)f(y)^{d-1}dy = 0` with
  `E = W - f ⊗ f`: `factorSolution_ortho`.  It is proved **pointwise in `x`**, for *every* `x`,
  not merely a.e.: the equation is assumed pointwise, and the subtracted term evaluates to
  `f(x)∫f^d = q f(x)` exactly.  The a.e. form demanded by `FactorDecomp.ortho` is the
  specialisation.
* `eq:rank-one-reduction-bounds`, `‖f - u_*‖₄ + ‖E‖₄ ≤ Cε` with `ε = ‖W - r_*‖₄`:
  `factorSolution_closeness`, with the explicit `C = factorSolutionCloseConst d`.  The proof is
  the paper's own scalar argument: with `U = W - r_*` and `b := r_*(∫f^{d-1})/q` one has
  `f - b = q^{-1}T_U(f^{d-1})` exactly (`factorSolution_sub_b_eq`), so `‖f - b‖₄ = O(ε)`; then
  `q = b^d + O(ε)` and `qb = r_*b^{d-1} + O(ε)` force `b^{d-1}(b² - r_*) = O(ε)`, and `b` is
  bounded away from `0` and `∞`, whence `b = u_* + O(ε)`.
* `exists_factorDecomp_of_solution` — the join point: the hypothesis list above yields a term of
  `SingularEndpoint/LocalizationRankOne/Factor.lean`'s `FactorDecomp d W` whose factor is `f` and whose `qVal` is `q`.

## The lower bound on `q`

`FactorDecomp.f_bdd` demands `f x ≤ 2`, which is **strictly stronger** than the invariant-set
bound `f ≤ M = 2/r_* ∈ (2,4]`.  It comes from `f ≤ q^{-1/d}`, and therefore needs `q` bounded
below.  No such bound follows from the hypothesis list: for the constant graphon `W ≡ c` the
constant `f ≡ √c` solves the equation with `q = c^{d/2}`, and `q^{-1/d} = c^{-1/2} → ∞` as
`c → 0`.  So a lower bound must be **assumed**, and the weakest one that does the job is
`hqlow : 1/2^d ≤ q`, i.e. exactly `q^{-1/d} ≤ 2`.  It is a hypothesis of seven statements in
this file — `factorSolution_le_two`, `exists_factorDecomp_of_solution`,
`factorSolution_b_upper`, `factorSolution_b_le_contractionM`, `factorSolution_abs_b_sub_uStar_le`,
`factorSolution_Lnorm_sub_uStar_le` and `factorSolution_closeness` — and of no other statement
here.  (Along the family `q → u_*^d = r_*^{d/2} ≥ 2^{-d/2}`, so it holds with room to
spare, but proving that needs the smallness of `ε`, which the pointwise bound does not.)

## Contents

* `factorSolution_amgm` — the scalar AM–GM `n t a^{n-1} ≤ (n-1)a^n + t^n`;
* `factorSolution_rpow_mul_integral_le` — `q^{1/d}∫f^{d-1} ≤ q` (Jensen on a probability space);
* `factorSolution_qVal_mul_le` — `q f(x) ≤ ∫ f^{d-1}` (from `W ≤ 1`);
* `factorSolution_pointwise_bound`, `factorSolution_le_two` —
  the pointwise bound of `eq:rank-one-orthogonality` and its `f ≤ 2` consequence;
* `factorSolution_ortho` — the orthogonality half of `eq:rank-one-orthogonality`,
  pointwise;
* `exists_factorDecomp_of_solution` — the `FactorDecomp` builder;
* `factorSolutionB` and `factorSolution_num_split`, `factorSolution_sub_b_eq`,
  `factorSolution_Lnorm_err_le`, `factorSolution_Lnorm_sub_b_le` — the scalar `b` and the exact
  identity `f - b = q^{-1}T_U(f^{d-1})` in `L⁴`;
* `factorSolution_abs_integral_sub_pow_le`, `factorSolution_b_nonneg`,
  `factorSolution_b_lower`, `factorSolution_b_upper`, `factorSolution_b_le_contractionM`,
  `factorSolution_abs_b_sub_uStar_le` — the moment comparison and the scalar step `b = u_* + O(ε)`;
* `factorSolutionDelta`, `factorSolutionK1`, `factorSolutionBeta`, `factorSolutionK2`,
  `factorSolutionCloseConst` and their positivity lemmas — the explicit constants;
* `factorSolution_Lnorm_sub_uStar_le`, `factorSolution_Lnorm_resid_le`,
  `factorSolution_closeness` — the two halves of `eq:rank-one-reduction-bounds` and their sum;
* `factorSolution_abs_pow_le`, `factorSolution_integrable_pow`,
  `factorSolution_integrable_kernel_pow` — the boundedness/integrability plumbing;
* `factorSolutionLnorm_add_le`, `factorSolutionLnorm_neg` — Minkowski at `p = 4` for a general
  finite measure, and the sign-invariance of `Lnorm`, shared with `SingularEndpoint/LocalizationRankOne/FactorMain.lean`.
-/

namespace UpperTailOptimizers

open MeasureTheory

variable {d : ℕ} {W : Graphon} {f : ℝ → ℝ} {q : ℝ}

/-! ## Bounded-function tools

The same `integrable_of_abs_le` idiom as in `SingularEndpoint/LocalizationRankOne/KernelOp.lean` and
`SingularEndpoint/LocalizationRankOne/FactorContraction.lean`; it is `private` in both, hence repeated here under a
file-specific name.
-/

/-- `|f^k| ≤ M^k` for a factor with values in `[0, M]`. -/
theorem factorSolution_abs_pow_le (hnn : ∀ x, 0 ≤ f x) (hMb : ∀ x, f x ≤ contractionM d) (k : ℕ)
    (y : ℝ) : |f y ^ k| ≤ contractionM d ^ k := by
  rw [abs_pow, abs_of_nonneg (hnn y)]
  exact pow_le_pow_left₀ (hnn y) (hMb y) k

/-- Every power of the factor is integrable on `[0,1]`. -/
theorem factorSolution_integrable_pow (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (k : ℕ) : Integrable (fun y => f y ^ k) unitμ :=
  integrable_of_abs_le (hmeas.pow_const k) _
    (factorSolution_abs_pow_le hnn hMb k)

/-- `y ↦ W(x,y) f(y)^k` is integrable for each fixed `x`. -/
theorem factorSolution_integrable_kernel_pow (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (x : ℝ) (k : ℕ) :
    Integrable (fun y => W.toFun x y * f y ^ k) unitμ := by
  refine integrable_of_abs_le
    ((measurable_toFun_right W x).mul (hmeas.pow_const k)) (1 * contractionM d ^ k) fun y => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_le.mpr ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩)
    (factorSolution_abs_pow_le hnn hMb k y) (abs_nonneg _) zero_le_one

/-! ## The scalar AM–GM -/

/-- **The scalar inequality behind the Hölder step of the pointwise bound** (the second half
of `eq:rank-one-orthogonality`): for `a, t ≥ 0` and `n ≥ 1`,

`n·t·a^{n-1} ≤ (n-1)·a^n + t^n`.

This is the arithmetic–geometric mean inequality for `n-1` copies of `a^n` and one copy of
`t^n`; the proof given is Bernoulli's inequality `(1+x)^n ≥ 1 + nx` at `x = t/a - 1`, rescaled
by `a^n`.  The degenerate value `a = 0` is treated separately, `a^{n-1}` being `1` when `n = 1`
and `0` otherwise. -/
theorem factorSolution_amgm {n : ℕ} (hn : 1 ≤ n) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (n : ℝ) * t * a ^ (n - 1) ≤ ((n : ℝ) - 1) * a ^ n + t ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · rcases eq_or_lt_of_le ha with ha0 | hapos
    · rw [← ha0, zero_pow (by omega : m ≠ 0), zero_pow (by omega : m + 1 ≠ 0)]
      simpa using pow_nonneg ht (m + 1)
    · have hane : a ≠ 0 := ne_of_gt hapos
      have hx : (-2 : ℝ) ≤ t / a - 1 := by
        have h0 : 0 ≤ t / a := div_nonneg ht hapos.le
        linarith
      have hb := one_add_mul_le_pow hx (m + 1)
      push_cast at hb
      rw [show (1 : ℝ) + (t / a - 1) = t / a from by ring] at hb
      have e3 : a * (t / a) = t := by field_simp
      have key := mul_le_mul_of_nonneg_left hb (pow_nonneg hapos.le (m + 1))
      have e1 : a ^ (m + 1) * (t / a) ^ (m + 1) = t ^ (m + 1) := by
        rw [← mul_pow, e3]
      have e2 : a ^ (m + 1) * (1 + ((m : ℝ) + 1) * (t / a - 1))
          = ((m : ℝ) + 1) * t * a ^ m - (m : ℝ) * a ^ (m + 1) := by
        rw [pow_succ]
        linear_combination (((m : ℝ) + 1) * a ^ m) * e3
      rw [e1, e2] at key
      linarith

/-! ## The pointwise bound of `eq:rank-one-orthogonality` -/

/-- **The Hölder/Jensen step of the pointwise bound** `eq:rank-one-orthogonality`,
in the division-free form

`q^{1/d}·∫f^{d-1} ≤ q`   (equivalently `∫f^{d-1} ≤ q^{(d-1)/d}`).

Only `0 ≤ f ≤ M` and `q = ∫f^d` are used; the Factor equation plays no part.  The proof is
`factorSolution_amgm` at `t = q^{1/d}` integrated over the probability space `unitμ`, which
turns into `d·t·∫f^{d-1} ≤ (d-1)q + t^d = d·q`. -/
theorem factorSolution_rpow_mul_integral_le (hd : 2 ≤ d) (hmeas : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 ≤ q)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) :
    q ^ ((d : ℝ)⁻¹) * ∫ x, f x ^ (d - 1) ∂unitμ ≤ q := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have h : 0 < d := by omega
    exact_mod_cast h
  have htnn : (0 : ℝ) ≤ q ^ ((d : ℝ)⁻¹) := Real.rpow_nonneg hq _
  have htd : (q ^ ((d : ℝ)⁻¹)) ^ d = q := Real.rpow_inv_natCast_pow hq (by omega)
  have hi1 : Integrable (fun x => f x ^ (d - 1)) unitμ :=
    factorSolution_integrable_pow hmeas hnn hMb (d - 1)
  have hi2 : Integrable (fun x => f x ^ d) unitμ :=
    factorSolution_integrable_pow hmeas hnn hMb d
  have hmono := integral_mono (hi1.const_mul ((d : ℝ) * q ^ ((d : ℝ)⁻¹)))
    ((hi2.const_mul ((d : ℝ) - 1)).add (integrable_const ((q ^ ((d : ℝ)⁻¹)) ^ d)))
    (fun x => factorSolution_amgm (by omega : 1 ≤ d) (hnn x) htnn)
  have hc : ∫ _x : ℝ, ((q ^ ((d : ℝ)⁻¹)) ^ d) ∂unitμ = q := by
    rw [integral_const]
    simp [htd]
  simp only [Pi.add_apply] at hmono
  rw [integral_const_mul, integral_add (hi2.const_mul _) (integrable_const _),
    integral_const_mul, hc, ← hqdef] at hmono
  have hfin : (d : ℝ) * (q ^ ((d : ℝ)⁻¹) * ∫ x, f x ^ (d - 1) ∂unitμ) ≤ (d : ℝ) * q := by
    rw [← mul_assoc]
    linarith
  exact le_of_mul_le_mul_left hfin hdpos

/-- **The elementary step of the pointwise bound of `eq:rank-one-orthogonality`**:
`q f(x) ≤ ∫ f^{d-1}` for
*every* `x`, because `W ≤ 1` and `f ≥ 0`.  (`FactorDecomp.qVal_mul_f_le` is the a.e. version
derived from the structure; this one is pointwise, from the pointwise equation.) -/
theorem factorSolution_qVal_mul_le (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x) (x : ℝ) :
    q * f x ≤ ∫ y, f y ^ (d - 1) ∂unitμ := by
  rw [← heq x]
  refine integral_mono (factorSolution_integrable_kernel_pow hmeas hnn hMb x (d - 1))
    (factorSolution_integrable_pow hmeas hnn hMb (d - 1)) fun y => ?_
  exact mul_le_of_le_one_left (pow_nonneg (hnn y) _) (W.le_one' x y)

/-- **The pointwise bound of `eq:rank-one-orthogonality`**: every nonnegative solution
of the nonlinear Factor equation obeys `f(x) ≤ q^{-1/d}`.

The chain is `q f(x) = ∫W(x,y)f(y)^{d-1}dy ≤ ∫f^{d-1} ≤ q^{(d-1)/d}` — in the paper
an unlabelled display in the proof of `lem:localization-rank-one` — i.e.
`factorSolution_qVal_mul_le` followed by `factorSolution_rpow_mul_integral_le`. -/
theorem factorSolution_pointwise_bound (hd : 2 ≤ d) (hmeas : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) (x : ℝ) : f x ≤ q ^ (-((d : ℝ)⁻¹)) := by
  have htpos : (0 : ℝ) < q ^ ((d : ℝ)⁻¹) := Real.rpow_pos_of_pos hq _
  have hm := factorSolution_qVal_mul_le hmeas hnn hMb heq x
  have ht := factorSolution_rpow_mul_integral_le hd hmeas hnn hMb hq.le hqdef
  have h1 : q ^ ((d : ℝ)⁻¹) * (q * f x) ≤ q :=
    le_trans (mul_le_mul_of_nonneg_left hm htpos.le) ht
  have h2 : q * (q ^ ((d : ℝ)⁻¹) * f x) ≤ q * 1 := by
    rw [mul_one]
    linarith [h1, mul_comm (q ^ ((d : ℝ)⁻¹)) q]
  have h3 : q ^ ((d : ℝ)⁻¹) * f x ≤ 1 := le_of_mul_le_mul_left h2 hq
  have h4 : q ^ ((d : ℝ)⁻¹) * f x ≤ q ^ ((d : ℝ)⁻¹) * (q ^ ((d : ℝ)⁻¹))⁻¹ := by
    rw [mul_inv_cancel₀ htpos.ne']
    exact h3
  rw [Real.rpow_neg hq.le]
  exact le_of_mul_le_mul_left h4 htpos

/-- The bound `f x ≤ 2` demanded by `FactorDecomp.f_bdd`, under the lower bound `1/2^d ≤ q`.

This is `factorSolution_pointwise_bound` together with `q^{-1/d} ≤ 2`, which is *equivalent* to
`1/2^d ≤ q`.  See the module docstring: no lower bound on `q` follows from the other
hypotheses, so this one is assumed. -/
theorem factorSolution_le_two (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) (hqlow : (1 : ℝ) / 2 ^ d ≤ q) (x : ℝ) : f x ≤ 2 := by
  have hb := factorSolution_pointwise_bound hd hmeas hnn hMb hq heq hqdef x
  have hhalf : ((1 : ℝ) / 2) ^ d ≤ q := by
    rw [div_pow, one_pow]
    exact hqlow
  have h1 : (1 : ℝ) / 2 ≤ q ^ ((d : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by positivity) hhalf (by positivity : (0 : ℝ) ≤ ((d : ℝ)⁻¹))
    rwa [Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2) (by omega)] at h
  have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) h1
  norm_num at h2
  rw [Real.rpow_neg hq.le] at hb
  linarith

/-! ## The orthogonality half of `eq:rank-one-orthogonality` -/

/-- **The second identity of `eq:rank-one-orthogonality`**, `∫E(x,y)f(y)^{d-1}dy = 0` for
the residual `E = W - f ⊗ f`.

The paper states it for a.e. `x`; from the *pointwise* Factor equation it holds for **every**
`x`, which is what is proved here.  Indeed
`∫(W(x,y) - f(x)f(y))f(y)^{d-1}dy = q f(x) - f(x)∫f^d = q f(x) - q f(x) = 0`, using `1 ≤ d` to
collapse `f·f^{d-1}` to `f^d`. -/
theorem factorSolution_ortho (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) (x : ℝ) :
    ∫ y, (W.toFun x y - f x * f y) * f y ^ (d - 1) ∂unitμ = 0 := by
  have hpow : ∀ y : ℝ, f y * f y ^ (d - 1) = f y ^ d := by
    intro y
    calc f y * f y ^ (d - 1) = f y ^ (d - 1 + 1) := by ring
      _ = f y ^ d := by rw [show d - 1 + 1 = d from by omega]
  have hptw : ∀ y : ℝ, (W.toFun x y - f x * f y) * f y ^ (d - 1)
      = W.toFun x y * f y ^ (d - 1) - f x * f y ^ d := by
    intro y
    calc (W.toFun x y - f x * f y) * f y ^ (d - 1)
        = W.toFun x y * f y ^ (d - 1) - f x * (f y * f y ^ (d - 1)) := by ring
      _ = W.toFun x y * f y ^ (d - 1) - f x * f y ^ d := by rw [hpow y]
  rw [integral_congr_ae (Filter.Eventually.of_forall hptw),
    integral_sub (factorSolution_integrable_kernel_pow hmeas hnn hMb x (d - 1))
      ((factorSolution_integrable_pow hmeas hnn hMb d).const_mul _),
    integral_const_mul, ← hqdef]
  have hkey : ∫ y, W.toFun x y * f y ^ (d - 1) ∂unitμ = q * f x := heq x
  rw [hkey]
  ring

/-! ## The join point: building a `FactorDecomp` -/

/-- **The bridge to `SingularEndpoint/LocalizationRankOne/Factor.lean`.**  A pointwise solution of the nonlinear Factor
equation, with `q` bounded below by `2^{-d}`, is a `FactorDecomp d W` with factor `f` and
rank-one moment `q`.

All five data of the structure are discharged: `f` itself, `meas_f` and `f_nonneg` are
hypotheses, `f_bdd` is `factorSolution_le_two` (this is where `hqlow` is used, and the only
place it is needed for this theorem), and `ortho` is the a.e. weakening of the pointwise
`factorSolution_ortho`.  Everything `SingularEndpoint/LocalizationRankOne/Factor.lean` proves — `factor_eq`,
`linear_term_zero`, `Wmoment_eq` `eq:rank-one-reduction-bounds` — is thereby available for `f`. -/
theorem exists_factorDecomp_of_solution (hd : 2 ≤ d) (hmeas : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) (hqlow : (1 : ℝ) / 2 ^ d ≤ q) :
    ∃ P : FactorDecomp d W, (∀ x, P.f x = f x) ∧ P.qVal = q := by
  refine ⟨{ f := f
            meas_f := hmeas
            f_nonneg := hnn
            f_bdd := fun x => factorSolution_le_two hd hmeas hnn hMb hq heq hqdef hqlow x
            ortho := Filter.Eventually.of_forall
              fun x => factorSolution_ortho hd hmeas hnn hMb heq hqdef x }, fun _ => rfl, ?_⟩
  simpa [FactorDecomp.qVal] using hqdef.symm

/-! ## `L⁴` tools not provided by the layer below

`SingularEndpoint/LocalizationRankOne/FactorContraction.lean` proves Minkowski for `Lnorm` only at the measure `unitμ`; the
residual `E` lives on the square, so the same statement is needed at `gμ`.  The three lemmas
here are the general-measure versions, plus the two Fubini identities that identify the `L⁴`
functional of a one-variable function on the square with its `L⁴` functional on `[0,1]`.
-/

/-- `‖c‖₄ = |c|` for a constant on a probability space. -/
private theorem factorSolutionLnorm_const {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (c : ℝ) : Lnorm μ 4 (fun _ => c) = |c| := by
  have h1 : ∫ _x : α, |c| ^ (4 : ℝ) ∂μ = |c| ^ (4 : ℝ) := by simp
  rw [Lnorm, h1, ← Real.rpow_mul (abs_nonneg c)]
  norm_num

/-- `Lnorm` is insensitive to a sign change. -/
theorem factorSolutionLnorm_neg {α : Type*} [MeasurableSpace α] {μ : Measure α} (p : ℝ)
    (g : α → ℝ) : Lnorm μ p (fun x => -g x) = Lnorm μ p g := by
  unfold Lnorm
  refine congrArg (· ^ (1 / p)) (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
  simp only [abs_neg]

/-- **Minkowski at `p = 4` for a general finite measure.**  `contractionLnorm_add_le`
(`SingularEndpoint/LocalizationRankOne/FactorContraction.lean`) is stated only at `unitμ`; the residual `E` of
`eq:rank-one-reduction-bounds` lives on the square, so the same proof is repeated here for an
arbitrary finite measure. -/
theorem factorSolutionLnorm_add_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {g h : α → ℝ} (hg : Measurable g) (hh : Measurable h) {Cg Ch : ℝ}
    (hgb : ∀ x, |g x| ≤ Cg) (hhb : ∀ x, |h x| ≤ Ch) :
    Lnorm μ 4 (fun x => g x + h x) ≤ Lnorm μ 4 g + Lnorm μ 4 h := by
  have hmem : ∀ {u : α → ℝ} {C : ℝ}, Measurable u → (∀ x, |u x| ≤ C) → MemLp u 4 μ := by
    intro u C hu hb
    exact MemLp.of_bound hu.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)
  have key : ∀ {u : α → ℝ}, MemLp u 4 μ → eLpNorm u 4 μ = ENNReal.ofReal (Lnorm μ 4 u) := by
    intro u hu
    rw [hu.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp [Lnorm, Real.norm_eq_abs, one_div]
  have hmg := hmem hg hgb
  have hmh := hmem hh hhb
  have hsum : eLpNorm (g + h) 4 μ ≤ eLpNorm g 4 μ + eLpNorm h 4 μ :=
    eLpNorm_add_le (μ := μ) hg.aestronglyMeasurable hh.aestronglyMeasurable
      (by norm_num : (1 : ENNReal) ≤ 4)
  rw [key (hmg.add hmh), key hmg, key hmh,
    ← ENNReal.ofReal_add (Lnorm_nonneg _ _ _) (Lnorm_nonneg _ _ _)] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (Lnorm_nonneg _ _ _) (Lnorm_nonneg _ _ _))).mp hsum

/-- A function of the first coordinate has the same `L⁴` functional on the square as on the
interval. -/
private theorem factorSolutionLnorm_fst (g : ℝ → ℝ) :
    Lnorm gμ 4 (fun z : ℝ × ℝ => g z.1) = Lnorm unitμ 4 g := by
  have h := integral_prod_mul (μ := unitμ) (ν := unitμ) (fun x => |g x| ^ (4 : ℝ))
    (fun _ : ℝ => (1 : ℝ))
  rw [Lnorm, Lnorm]
  congr 1
  simpa [gμ] using h

/-- The second-coordinate companion of `factorSolutionLnorm_fst`. -/
private theorem factorSolutionLnorm_snd (g : ℝ → ℝ) :
    Lnorm gμ 4 (fun z : ℝ × ℝ => g z.2) = Lnorm unitμ 4 g := by
  have h := integral_prod_mul (μ := unitμ) (ν := unitμ) (fun _ : ℝ => (1 : ℝ))
    (fun y => |g y| ^ (4 : ℝ))
  rw [Lnorm, Lnorm]
  congr 1
  simpa [gμ] using h

/-! ## The scalar `b` and the first-order identity -/

/-- The scalar `b := r_*(∫f^{d-1})/q` of the quantitative part of
`lem:localization-rank-one`.  It is the constant that the Factor equation forces `f` to be
close to: `f - b = q^{-1}T_U(f^{d-1})` exactly (`factorSolution_sub_b_eq`). -/
noncomputable def factorSolutionB (d : ℕ) (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  rStar d * (∫ y, f y ^ (d - 1) ∂unitμ) / q

/-- **The rank-one splitting of the Factor numerator**,
`T_W(f^{d-1})(x) = r_*∫f^{d-1} + T_U(f^{d-1})(x)` with `U = W - r_*`.

This is `contractionNum_split` of `SingularEndpoint/LocalizationRankOne/FactorContraction.lean`, but for a factor `f` that is *not*
assumed to have unit mass — the Factor solution has `∫f ≈ u_* ≠ 1`, so `ContractionMem` is
unavailable and the two-line proof is repeated. -/
theorem factorSolution_num_split (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (x : ℝ) :
    kernelOp W.toFun (fun y => f y ^ (d - 1)) x
      = rStar d * (∫ y, f y ^ (d - 1) ∂unitμ) + contractionErr W d f x := by
  have hUm : Measurable fun y => contractionU W d x y := (contraction_measurable_U W d).of_uncurry_left
  have h2 : Integrable (fun y => contractionU W d x y * f y ^ (d - 1)) unitμ := by
    refine integrable_of_abs_le (hUm.mul (hmeas.pow_const (d - 1)))
      (1 * contractionM d ^ (d - 1)) fun y => ?_
    rw [abs_mul]
    exact mul_le_mul (contraction_abs_U_le hd W x y) (factorSolution_abs_pow_le hnn hMb (d - 1) y)
      (abs_nonneg _) zero_le_one
  have key : ∀ y : ℝ, W.toFun x y * f y ^ (d - 1)
      = rStar d * f y ^ (d - 1) + contractionU W d x y * f y ^ (d - 1) := by
    intro y
    simp only [contractionU]
    ring
  simp only [kernelOp, contractionErr]
  calc ∫ y, W.toFun x y * f y ^ (d - 1) ∂unitμ
      = ∫ y, (rStar d * f y ^ (d - 1) + contractionU W d x y * f y ^ (d - 1)) ∂unitμ :=
        integral_congr_ae (Filter.Eventually.of_forall key)
    _ = rStar d * (∫ y, f y ^ (d - 1) ∂unitμ)
          + ∫ y, contractionU W d x y * f y ^ (d - 1) ∂unitμ := by
        rw [integral_add ((factorSolution_integrable_pow hmeas hnn hMb (d - 1)).const_mul _) h2,
          integral_const_mul]

/-- **The exact first-order identity of the paper's quantitative estimate**:
`f(x) - b = q^{-1}T_U(f^{d-1})(x)` for every `x`.  The whole deviation of `f` from a constant
is carried by the residual kernel `U = W - r_*`. -/
theorem factorSolution_sub_b_eq (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x) (x : ℝ) :
    f x - factorSolutionB d f q = contractionErr W d f x / q := by
  have h := (heq x).symm.trans (factorSolution_num_split hd hmeas hnn hMb x)
  rw [eq_div_iff hq.ne', factorSolutionB, sub_mul, div_mul_cancel₀ _ hq.ne']
  linear_combination h

/-- `‖T_U(f^{d-1})‖₄ ≤ εM^{d-1}`, the `L⁴` size of the whole deviation. -/
theorem factorSolution_Lnorm_err_le (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) :
    Lnorm unitμ 4 (contractionErr W d f) ≤ contractionEps W d * contractionM d ^ (d - 1) := by
  simp only [contractionErr]
  refine le_trans (contractionLnorm_kernelOp_U_le hd W (hmeas.pow_const (d - 1))
    (factorSolution_abs_pow_le hnn hMb (d - 1))) ?_
  exact mul_le_mul_of_nonneg_left
    (contractionLnorm_le (by norm_num) (pow_nonneg (contractionM_pos hd).le _)
      (factorSolution_abs_pow_le hnn hMb (d - 1))) (contractionEps_nonneg W d)

/-- `‖f - b‖₄ ≤ εM^{d-1}/q`: the identity `factorSolution_sub_b_eq` in `L⁴`. -/
theorem factorSolution_Lnorm_sub_b_le (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x) :
    Lnorm unitμ 4 (fun x => f x - factorSolutionB d f q)
      ≤ contractionEps W d * contractionM d ^ (d - 1) / q := by
  have hErrm : Measurable (contractionErr W d f) :=
    measurable_kernelOp (contraction_measurable_U W d) (hmeas.pow_const (d - 1))
  have hErrb : ∀ x, |contractionErr W d f x| ≤ contractionM d ^ (d - 1) := fun x => by
    have h := abs_kernelOp_le (contraction_measurable_U W d) (hmeas.pow_const (d - 1))
      (contraction_abs_U_le hd W) (factorSolution_abs_pow_le hnn hMb (d - 1)) x
    simpa [contractionErr] using h
  have hstep : Lnorm unitμ 4 (fun x => f x - factorSolutionB d f q)
      ≤ 1 / q * Lnorm unitμ 4 (contractionErr W d f) := by
    refine contractionLnorm_le_const_mul (by norm_num) (div_nonneg zero_le_one hq.le) hErrm hErrb
      fun x => ?_
    rw [factorSolution_sub_b_eq hd hmeas hnn hMb hq heq x, abs_div, abs_of_pos hq]
    exact le_of_eq (by ring)
  calc Lnorm unitμ 4 (fun x => f x - factorSolutionB d f q)
      ≤ 1 / q * Lnorm unitμ 4 (contractionErr W d f) := hstep
    _ ≤ 1 / q * (contractionEps W d * contractionM d ^ (d - 1)) :=
        mul_le_mul_of_nonneg_left (factorSolution_Lnorm_err_le hd hmeas hnn hMb)
          (div_nonneg zero_le_one hq.le)
    _ = contractionEps W d * contractionM d ^ (d - 1) / q := by ring

/-! ## Moment comparison -/

/-- `|∫f^n - b^n| ≤ nM^{n-1}‖f - b‖₄` for any constant `b ∈ [0, M]`: the `L¹`-Lipschitz bound
for `t ↦ t^n` on `[0,M]` (`abs_pow_sub_pow_le_box`), followed by `‖·‖₁ ≤ ‖·‖₄`. -/
theorem factorSolution_abs_integral_sub_pow_le (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) {b : ℝ} (hb0 : 0 ≤ b) (hbM : b ≤ contractionM d) (n : ℕ) :
    |(∫ x, f x ^ n ∂unitμ) - b ^ n|
      ≤ (n : ℝ) * contractionM d ^ (n - 1) * Lnorm unitμ 4 (fun x => f x - b) := by
  have hMnn : (0 : ℝ) ≤ contractionM d ^ (n - 1) := pow_nonneg (hb0.trans hbM) _
  have hnM : (0 : ℝ) ≤ (n : ℝ) * contractionM d ^ (n - 1) :=
    mul_nonneg (Nat.cast_nonneg n) hMnn
  have hsubm : Measurable fun x => f x - b := hmeas.sub_const b
  have hsubb : ∀ x, |f x - b| ≤ contractionM d := fun x => by
    have h1 := hnn x
    have h2 := hMb x
    rw [abs_le]
    constructor <;> linarith
  have hsi : Integrable (fun x => f x - b) unitμ :=
    integrable_of_abs_le hsubm _ hsubb
  have hpow : Integrable (fun x => f x ^ n) unitμ :=
    factorSolution_integrable_pow hmeas hnn hMb n
  have hbound : ∀ x, |f x ^ n - b ^ n| ≤ (n : ℝ) * contractionM d ^ (n - 1) * |f x - b| :=
    fun x => abs_pow_sub_pow_le_box (hnn x) (hMb x) hb0 hbM n
  have hint1 : Integrable (fun x => f x ^ n - b ^ n) unitμ := hpow.sub (integrable_const _)
  calc |(∫ x, f x ^ n ∂unitμ) - b ^ n|
      = |∫ x, (f x ^ n - b ^ n) ∂unitμ| := by
        rw [integral_sub hpow (integrable_const _)]
        simp
    _ ≤ ∫ x, |f x ^ n - b ^ n| ∂unitμ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ((n : ℝ) * contractionM d ^ (n - 1) * |f x - b|) ∂unitμ :=
        integral_mono hint1.abs (hsi.abs.const_mul _) hbound
    _ = (n : ℝ) * contractionM d ^ (n - 1) * ∫ x, |f x - b| ∂unitμ := integral_const_mul _ _
    _ ≤ (n : ℝ) * contractionM d ^ (n - 1) * Lnorm unitμ 4 (fun x => f x - b) :=
        mul_le_mul_of_nonneg_left (contractionIntegral_abs_le_Lnorm_four hsubm hsubb) hnM

/-! ## The scalar `b` is trapped in a compact subinterval of `(0, ∞)` -/

/-- `b ≥ 0`. -/
theorem factorSolution_b_nonneg (hd : 2 ≤ d) (hnn : ∀ x, 0 ≤ f x) (hq : 0 < q) :
    0 ≤ factorSolutionB d f q :=
  div_nonneg (mul_nonneg (rStar_pos hd).le
    (integral_nonneg fun x => pow_nonneg (hnn x) _)) hq.le

/-- **`b` is bounded below**, by `β = r_*²/2`.  The input is `q = ∫f^d ≤ M∫f^{d-1}`, which is
just `f ≤ M`; this is what keeps `b^{d-1}` away from `0` in the scalar argument. -/
theorem factorSolution_b_lower (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q) (hqdef : q = ∫ x, f x ^ d ∂unitμ) :
    rStar d ^ 2 / 2 ≤ factorSolutionB d f q := by
  have hpt : ∀ x, f x ^ d ≤ contractionM d * f x ^ (d - 1) := by
    intro x
    have he : f x ^ (d - 1) * f x = f x ^ d := by
      rw [← pow_succ, show d - 1 + 1 = d from by omega]
    calc f x ^ d = f x ^ (d - 1) * f x := he.symm
      _ ≤ f x ^ (d - 1) * contractionM d :=
          mul_le_mul_of_nonneg_left (hMb x) (pow_nonneg (hnn x) _)
      _ = contractionM d * f x ^ (d - 1) := mul_comm _ _
  have hqM : q ≤ contractionM d * ∫ x, f x ^ (d - 1) ∂unitμ := by
    rw [hqdef, ← integral_const_mul]
    exact integral_mono (factorSolution_integrable_pow hmeas hnn hMb d)
      ((factorSolution_integrable_pow hmeas hnn hMb (d - 1)).const_mul _) hpt
  rw [factorSolutionB, le_div_iff₀ hq]
  have h1 : rStar d ^ 2 / 2 * q
      ≤ rStar d ^ 2 / 2 * (contractionM d * ∫ x, f x ^ (d - 1) ∂unitμ) :=
    mul_le_mul_of_nonneg_left hqM (by positivity)
  have h2 : rStar d ^ 2 / 2 * (contractionM d * ∫ x, f x ^ (d - 1) ∂unitμ)
      = rStar d * (∫ x, f x ^ (d - 1) ∂unitμ) := by
    linear_combination (rStar d * (∫ x, f x ^ (d - 1) ∂unitμ) / 2) * contractionM_mul_rStar hd
  linarith

/-- **`b` is bounded above**, by `2r_* < 2 < M`, using `1/2^d ≤ q`.  The input is the Hölder
bound `q^{1/d}∫f^{d-1} ≤ q` of `factorSolution_rpow_mul_integral_le`. -/
theorem factorSolution_b_upper (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q) (hqdef : q = ∫ x, f x ^ d ∂unitμ)
    (hqlow : (1 : ℝ) / 2 ^ d ≤ q) : factorSolutionB d f q ≤ 2 * rStar d := by
  have hmnn : (0 : ℝ) ≤ ∫ x, f x ^ (d - 1) ∂unitμ :=
    integral_nonneg fun x => pow_nonneg (hnn x) _
  have ht := factorSolution_rpow_mul_integral_le hd hmeas hnn hMb hq.le hqdef
  have hhalf : ((1 : ℝ) / 2) ^ d ≤ q := by
    rw [div_pow, one_pow]
    exact hqlow
  have h1 : (1 : ℝ) / 2 ≤ q ^ ((d : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by positivity) hhalf (by positivity : (0 : ℝ) ≤ ((d : ℝ)⁻¹))
    rwa [Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2) (by omega)] at h
  have hstep : (1 : ℝ) / 2 * ∫ x, f x ^ (d - 1) ∂unitμ
      ≤ q ^ ((d : ℝ)⁻¹) * ∫ x, f x ^ (d - 1) ∂unitμ :=
    mul_le_mul_of_nonneg_right h1 hmnn
  have hm2 : (∫ x, f x ^ (d - 1) ∂unitμ) ≤ 2 * q := by linarith
  rw [factorSolutionB, div_le_iff₀ hq]
  have hr := rStar_pos hd
  nlinarith [hm2, hr]

/-- `b ≤ M`: the form in which the upper bound is consumed by
`factorSolution_abs_integral_sub_pow_le`.  `2r_* ≤ M = 2/r_*` because `r_* < 1`. -/
theorem factorSolution_b_le_contractionM (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q) (hqdef : q = ∫ x, f x ^ d ∂unitμ)
    (hqlow : (1 : ℝ) / 2 ^ d ≤ q) : factorSolutionB d f q ≤ contractionM d := by
  have hup := factorSolution_b_upper hd hmeas hnn hMb hq hqdef hqlow
  have hr := rStar_pos hd
  have hr1 := rStar_lt_one hd
  have hMr := contractionM_mul_rStar hd
  nlinarith [hup, hr, hr1, hMr]

/-! ## The constants of `eq:rank-one-reduction-bounds`

All four depend only on `d`.  `Δ` is the size of `‖f - b‖₄` in units of `ε`; `K₁` is the
numerator of the scalar estimate `b^{d-1}|b² - r_*| ≤ K₁‖f - b‖₄`; `β` is the lower bound for
`b`; `K₂` converts `‖f - b‖₄` into `‖f - u_*‖₄`.
-/

/-- `Δ(d) = 2^d M^{d-1}`, the constant in `‖f - b‖₄ ≤ Δ·ε` (the factor `2^d` is `1/q`, bounded
through `hqlow`). -/
noncomputable def factorSolutionDelta (d : ℕ) : ℝ := 2 ^ d * contractionM d ^ (d - 1)

/-- `K₁(d) = r_*(d-1)M^{d-2} + dM^d`, the numerator of the scalar estimate. -/
noncomputable def factorSolutionK1 (d : ℕ) : ℝ :=
  rStar d * (((d : ℝ) - 1) * contractionM d ^ (d - 2)) + (d : ℝ) * contractionM d ^ d

/-- `β(d) = r_*²/2`, the lower bound for the scalar `b` (`factorSolution_b_lower`). -/
noncomputable def factorSolutionBeta (d : ℕ) : ℝ := rStar d ^ 2 / 2

/-- `K₂(d) = 1 + K₁/(β^{d-1}u_*)`, so that `‖f - u_*‖₄ ≤ K₂‖f - b‖₄`. -/
noncomputable def factorSolutionK2 (d : ℕ) : ℝ :=
  1 + factorSolutionK1 d / (factorSolutionBeta d ^ (d - 1) * uStar d)

/-- **The constant `C` of `eq:rank-one-reduction-bounds`**,
`C = 1 + (1 + u_* + M)·K₂·Δ`. -/
noncomputable def factorSolutionCloseConst (d : ℕ) : ℝ :=
  1 + (1 + uStar d + contractionM d) * (factorSolutionK2 d * factorSolutionDelta d)

/-- `β(d) > 0`. -/
theorem factorSolutionBeta_pos (hd : 2 ≤ d) : 0 < factorSolutionBeta d := by
  have := rStar_pos hd
  simp only [factorSolutionBeta]
  positivity

/-- `K₁(d) ≥ 0`. -/
theorem factorSolutionK1_nonneg (hd : 2 ≤ d) : 0 ≤ factorSolutionK1 d := by
  have hr := rStar_pos hd
  have hM := contractionM_pos hd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h1 : (0 : ℝ) ≤ contractionM d ^ (d - 2) := pow_nonneg hM.le _
  have h2 : (0 : ℝ) ≤ contractionM d ^ d := pow_nonneg hM.le _
  have t1 : (0 : ℝ) ≤ rStar d * (((d : ℝ) - 1) * contractionM d ^ (d - 2)) :=
    mul_nonneg hr.le (mul_nonneg (by linarith) h1)
  have t2 : (0 : ℝ) ≤ (d : ℝ) * contractionM d ^ d := mul_nonneg (by linarith) h2
  simp only [factorSolutionK1]
  linarith

/-- `K₂(d) ≥ 0`. -/
theorem factorSolutionK2_nonneg (hd : 2 ≤ d) : 0 ≤ factorSolutionK2 d := by
  have hK1 := factorSolutionK1_nonneg hd
  have hβ := factorSolutionBeta_pos hd
  have hu := uStar_pos hd
  have hden : (0 : ℝ) < factorSolutionBeta d ^ (d - 1) * uStar d :=
    mul_pos (pow_pos hβ _) hu
  simp only [factorSolutionK2]
  positivity

/-- `Δ(d) ≥ 0`. -/
theorem factorSolutionDelta_nonneg (hd : 2 ≤ d) : 0 ≤ factorSolutionDelta d := by
  have hM := contractionM_pos hd
  simp only [factorSolutionDelta]
  positivity

/-! ## The scalar step: `b = u_* + O(ε)` -/

/-- **The paper's scalar argument, isolated.**  Given `b ∈ [β, M]`, the exact relation
`bq = r_*m` and the two moment estimates `|q - b^d| ≤ dM^{d-1}δ`,
`|m - b^{d-1}| ≤ (d-1)M^{d-2}δ`, one gets `b = u_* + O(δ)`.

The mechanism is the identity
`b^{d-1}(b² - r_*) = r_*(m - b^{d-1}) + b(b^d - q)`,
which holds *because* `bq = r_*m`; the left-hand side is bounded below by
`β^{d-1}|b² - r_*|`, and `b² - r_* = (b - u_*)(b + u_*)` with `b + u_* ≥ u_* > 0`.

Stated for plain scalars, with no reference to `f`, `W` or any integral. -/
private theorem factorSolution_scalar_b (hd : 2 ≤ d) {b m qq δ : ℝ} (hb0 : 0 ≤ b)
    (hbM : b ≤ contractionM d) (hblow : factorSolutionBeta d ≤ b) (_hδ0 : 0 ≤ δ)
    (hbq : b * qq = rStar d * m)
    (hA1 : |qq - b ^ d| ≤ (d : ℝ) * contractionM d ^ (d - 1) * δ)
    (hA2 : |m - b ^ (d - 1)| ≤ ((d : ℝ) - 1) * contractionM d ^ (d - 2) * δ) :
    |b - uStar d| ≤ factorSolutionK1 d / (factorSolutionBeta d ^ (d - 1) * uStar d) * δ := by
  have hr := rStar_pos hd
  have hM := contractionM_pos hd
  have hu := uStar_pos hd
  have hβ := factorSolutionBeta_pos hd
  have hβpow : (0 : ℝ) < factorSolutionBeta d ^ (d - 1) := pow_pos hβ _
  have hA1' : |b ^ d - qq| ≤ (d : ℝ) * contractionM d ^ (d - 1) * δ := by rwa [abs_sub_comm]
  have hpowid : b ^ (d - 1) * b ^ 2 = b * b ^ d := by
    rw [← pow_add, ← pow_succ', show d - 1 + 2 = d + 1 from by omega]
  have hid : b ^ (d - 1) * (b ^ 2 - rStar d)
      = rStar d * (m - b ^ (d - 1)) + b * (b ^ d - qq) := by
    linear_combination hpowid + hbq
  have habs : b ^ (d - 1) * |b ^ 2 - rStar d| ≤ factorSolutionK1 d * δ := by
    have hPnn : (0 : ℝ) ≤ b ^ (d - 1) := pow_nonneg hb0 _
    calc b ^ (d - 1) * |b ^ 2 - rStar d| = |b ^ (d - 1) * (b ^ 2 - rStar d)| := by
          rw [abs_mul, abs_of_nonneg hPnn]
      _ = |rStar d * (m - b ^ (d - 1)) + b * (b ^ d - qq)| := by rw [hid]
      _ ≤ |rStar d * (m - b ^ (d - 1))| + |b * (b ^ d - qq)| := abs_add_le _ _
      _ = rStar d * |m - b ^ (d - 1)| + b * |b ^ d - qq| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hr.le, abs_of_nonneg hb0]
      _ ≤ rStar d * (((d : ℝ) - 1) * contractionM d ^ (d - 2) * δ)
            + contractionM d * ((d : ℝ) * contractionM d ^ (d - 1) * δ) := by
          have h1 : rStar d * |m - b ^ (d - 1)|
              ≤ rStar d * (((d : ℝ) - 1) * contractionM d ^ (d - 2) * δ) :=
            mul_le_mul_of_nonneg_left hA2 hr.le
          have h2 : b * |b ^ d - qq| ≤ contractionM d * ((d : ℝ) * contractionM d ^ (d - 1) * δ) :=
            mul_le_mul hbM hA1' (abs_nonneg _) hM.le
          linarith
      _ = factorSolutionK1 d * δ := by
          simp only [factorSolutionK1]
          linear_combination ((d : ℝ) * δ) * contractionM_mul_pow hd
  have hbeta : factorSolutionBeta d ^ (d - 1) * |b ^ 2 - rStar d| ≤ factorSolutionK1 d * δ :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hβ.le hblow (d - 1))
      (abs_nonneg _)) habs
  have habs2 : |b ^ 2 - rStar d| ≤ factorSolutionK1 d * δ / factorSolutionBeta d ^ (d - 1) := by
    rw [le_div_iff₀ hβpow, mul_comm]
    exact hbeta
  have hsq : (b + uStar d) * |b - uStar d| = |b ^ 2 - rStar d| := by
    rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ b + uStar d), ← abs_mul]
    congr 1
    linear_combination -(uStar_sq hd)
  have hfin : uStar d * |b - uStar d| ≤ |b ^ 2 - rStar d| := by
    rw [← hsq]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hstep : |b - uStar d|
      ≤ factorSolutionK1 d * δ / factorSolutionBeta d ^ (d - 1) / uStar d := by
    rw [le_div_iff₀ hu, mul_comm]
    exact le_trans hfin habs2
  refine le_trans hstep (le_of_eq ?_)
  rw [div_div, div_mul_eq_mul_div]

/-- **`b = u_* + O(‖f - b‖₄)`**: `factorSolution_scalar_b` instantiated at the Factor data.
This is where `u_*` finally enters the argument — it is *derived*, not assumed: `b² = r_*` up
to `O(‖f - b‖₄)` and `u_* = √r_*`. -/
theorem factorSolution_abs_b_sub_uStar_le (hd : 2 ≤ d) (hmeas : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) (hqlow : (1 : ℝ) / 2 ^ d ≤ q) :
    |factorSolutionB d f q - uStar d|
      ≤ factorSolutionK1 d / (factorSolutionBeta d ^ (d - 1) * uStar d)
        * Lnorm unitμ 4 (fun x => f x - factorSolutionB d f q) := by
  have hb0 := factorSolution_b_nonneg hd hnn hq
  have hbM := factorSolution_b_le_contractionM hd hmeas hnn hMb hq hqdef hqlow
  have hbq : factorSolutionB d f q * q = rStar d * ∫ x, f x ^ (d - 1) ∂unitμ :=
    div_mul_cancel₀ _ hq.ne'
  have hA1 : |q - factorSolutionB d f q ^ d|
      ≤ (d : ℝ) * contractionM d ^ (d - 1) * Lnorm unitμ 4 (fun x => f x - factorSolutionB d f q) := by
    have h := factorSolution_abs_integral_sub_pow_le hmeas hnn hMb hb0 hbM d
    rwa [← hqdef] at h
  have hA2 : |(∫ x, f x ^ (d - 1) ∂unitμ) - factorSolutionB d f q ^ (d - 1)|
      ≤ ((d : ℝ) - 1) * contractionM d ^ (d - 2)
        * Lnorm unitμ 4 (fun x => f x - factorSolutionB d f q) := by
    have h := factorSolution_abs_integral_sub_pow_le hmeas hnn hMb hb0 hbM (d - 1)
    rwa [show ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 from by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one],
      show d - 1 - 1 = d - 2 from by omega] at h
  exact factorSolution_scalar_b hd hb0 hbM
    (factorSolution_b_lower hd hmeas hnn hMb hq hqdef) (Lnorm_nonneg _ _ _) hbq hA1 hA2

/-! ## The two halves of `eq:rank-one-reduction-bounds` -/

/-- **`‖f - u_*‖₄ ≤ K₂Δ·ε`**, the first half of `eq:rank-one-reduction-bounds`. -/
theorem factorSolution_Lnorm_sub_uStar_le (hd : 2 ≤ d) (hmeas : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) (hqlow : (1 : ℝ) / 2 ^ d ≤ q) :
    Lnorm unitμ 4 (fun x => f x - uStar d)
      ≤ factorSolutionK2 d * (factorSolutionDelta d * contractionEps W d) := by
  have hb0 := factorSolution_b_nonneg hd hnn hq
  have hbM := factorSolution_b_le_contractionM hd hmeas hnn hMb hq hqdef hqlow
  have hsubb : ∀ x, |f x - factorSolutionB d f q| ≤ contractionM d := fun x => by
    have h1 := hnn x
    have h2 := hMb x
    rw [abs_le]
    constructor <;> linarith
  have hqinv : 1 / q ≤ 2 ^ d := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / 2 ^ d) hqlow
    rwa [one_div_one_div] at h
  have hδΔ : Lnorm unitμ 4 (fun x => f x - factorSolutionB d f q)
      ≤ factorSolutionDelta d * contractionEps W d := by
    refine le_trans (factorSolution_Lnorm_sub_b_le hd hmeas hnn hMb hq heq) ?_
    have hnn2 : (0 : ℝ) ≤ contractionEps W d * contractionM d ^ (d - 1) :=
      mul_nonneg (contractionEps_nonneg W d) (pow_nonneg (contractionM_pos hd).le _)
    rw [div_eq_mul_one_div]
    calc contractionEps W d * contractionM d ^ (d - 1) * (1 / q)
        ≤ contractionEps W d * contractionM d ^ (d - 1) * 2 ^ d :=
          mul_le_mul_of_nonneg_left hqinv hnn2
      _ = factorSolutionDelta d * contractionEps W d := by
          simp only [factorSolutionDelta]
          ring
  have hcong : Lnorm unitμ 4 (fun x => f x - uStar d)
      = Lnorm unitμ 4 (fun x => (f x - factorSolutionB d f q)
          + (factorSolutionB d f q - uStar d)) :=
    lpBridge_Lnorm_congr 4 (Filter.Eventually.of_forall fun x => by ring)
  have hmink := factorSolutionLnorm_add_le (μ := unitμ) (hmeas.sub_const (factorSolutionB d f q))
    (measurable_const (a := factorSolutionB d f q - uStar d)) hsubb
    (fun _ => le_refl |factorSolutionB d f q - uStar d|)
  rw [factorSolutionLnorm_const] at hmink
  have hbu := factorSolution_abs_b_sub_uStar_le hd hmeas hnn hMb hq hqdef hqlow
  have hK2 : Lnorm unitμ 4 (fun x => f x - uStar d)
      ≤ factorSolutionK2 d * Lnorm unitμ 4 (fun x => f x - factorSolutionB d f q) := by
    rw [hcong]
    refine le_trans hmink ?_
    simp only [factorSolutionK2]
    have := hbu
    nlinarith [this]
  refine le_trans hK2 (mul_le_mul_of_nonneg_left hδΔ (factorSolutionK2_nonneg hd))

/-- **The residual half of `eq:rank-one-reduction-bounds`**:
`‖E‖₄ ≤ ε + (u_* + M)‖f - u_*‖₄` for `E = W - f ⊗ f`.

The splitting is `E = U + (r_* - f ⊗ f)` and
`r_* - f(x)f(y) = (u_* - f(x))u_* + f(x)(u_* - f(y))`, which is where `u_*² = r_*` is used. -/
theorem factorSolution_Lnorm_resid_le (hd : 2 ≤ d) (hmeas : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) (hMb : ∀ x, f x ≤ contractionM d) :
    Lnorm gμ 4 (fun z : ℝ × ℝ => W.toFun z.1 z.2 - f z.1 * f z.2)
      ≤ contractionEps W d + (uStar d + contractionM d) * Lnorm unitμ 4 (fun x => f x - uStar d) := by
  have hM := contractionM_pos hd
  have hu0 := uStar_nonneg hd
  have hu1 := (uStar_lt_one hd).le
  have hMgt : (2 : ℝ) < contractionM d := by
    have hr1 := rStar_lt_one hd
    have hr := rStar_pos hd
    have hMr := contractionM_mul_rStar hd
    nlinarith [hr, hr1, hMr]
  have hufb : ∀ x, |uStar d - f x| ≤ contractionM d := fun x => by
    have h1 := hnn x
    have h2 := hMb x
    rw [abs_le]
    constructor <;> linarith
  have hUm : Measurable fun z : ℝ × ℝ => contractionU W d z.1 z.2 := contraction_measurable_U W d
  have hfstm : Measurable fun z : ℝ × ℝ => uStar d - f z.1 :=
    measurable_const.sub (hmeas.comp measurable_fst)
  have hsndm : Measurable fun z : ℝ × ℝ => uStar d - f z.2 :=
    measurable_const.sub (hmeas.comp measurable_snd)
  have hRm : Measurable fun z : ℝ × ℝ => rStar d - f z.1 * f z.2 :=
    measurable_const.sub ((hmeas.comp measurable_fst).mul (hmeas.comp measurable_snd))
  have hRb : ∀ z : ℝ × ℝ, |rStar d - f z.1 * f z.2| ≤ 1 + contractionM d ^ 2 := fun z => by
    have h1 := (rStar_pos hd).le
    have h2 := (rStar_lt_one hd).le
    have h3 := hnn z.1
    have h4 := hMb z.1
    have h5 := hnn z.2
    have h6 := hMb z.2
    have h7 : f z.1 * f z.2 ≤ contractionM d ^ 2 := by nlinarith
    have h8 : 0 ≤ f z.1 * f z.2 := mul_nonneg h3 h5
    rw [abs_le]
    constructor <;> nlinarith
  have hAm : Measurable fun z : ℝ × ℝ => (uStar d - f z.1) * uStar d := hfstm.mul_const _
  have hBm : Measurable fun z : ℝ × ℝ => f z.1 * (uStar d - f z.2) :=
    (hmeas.comp measurable_fst).mul hsndm
  have hAb : ∀ z : ℝ × ℝ, |(uStar d - f z.1) * uStar d| ≤ contractionM d := fun z => by
    rw [abs_mul, abs_of_nonneg hu0]
    calc |uStar d - f z.1| * uStar d ≤ contractionM d * 1 :=
          mul_le_mul (hufb z.1) hu1 hu0 hM.le
      _ = contractionM d := mul_one _
  have hBb : ∀ z : ℝ × ℝ, |f z.1 * (uStar d - f z.2)| ≤ contractionM d * contractionM d := fun z => by
    rw [abs_mul]
    exact mul_le_mul (by rw [abs_of_nonneg (hnn z.1)]; exact hMb z.1) (hufb z.2)
      (abs_nonneg _) hM.le
  -- split off the residual kernel `U`
  have hcong : Lnorm gμ 4 (fun z : ℝ × ℝ => W.toFun z.1 z.2 - f z.1 * f z.2)
      = Lnorm gμ 4 (fun z : ℝ × ℝ => contractionU W d z.1 z.2 + (rStar d - f z.1 * f z.2)) :=
    lpBridge_Lnorm_congr 4 (Filter.Eventually.of_forall fun z => by
      simp only [contractionU]; ring)
  have hm1 := factorSolutionLnorm_add_le (μ := gμ) hUm hRm
    (fun z : ℝ × ℝ => contraction_abs_U_le hd W z.1 z.2) hRb
  -- split the rank-one defect
  have hcong2 : Lnorm gμ 4 (fun z : ℝ × ℝ => rStar d - f z.1 * f z.2)
      = Lnorm gμ 4 (fun z : ℝ × ℝ => (uStar d - f z.1) * uStar d + f z.1 * (uStar d - f z.2)) :=
    lpBridge_Lnorm_congr 4 (Filter.Eventually.of_forall fun z => by
      linear_combination -(uStar_sq hd))
  have hm2 := factorSolutionLnorm_add_le (μ := gμ) hAm hBm hAb hBb
  -- the two one-variable terms
  have hLfst : Lnorm unitμ 4 (fun x => uStar d - f x) = Lnorm unitμ 4 (fun x => f x - uStar d) := by
    rw [lpBridge_Lnorm_congr 4 (μ := unitμ) (f := fun x => uStar d - f x)
      (g := fun x => -(f x - uStar d)) (Filter.Eventually.of_forall fun x => by ring)]
    exact factorSolutionLnorm_neg 4 _
  have hA : Lnorm gμ 4 (fun z : ℝ × ℝ => (uStar d - f z.1) * uStar d)
      ≤ uStar d * Lnorm unitμ 4 (fun x => f x - uStar d) := by
    have h : Lnorm gμ 4 (fun z : ℝ × ℝ => (uStar d - f z.1) * uStar d)
        ≤ uStar d * Lnorm gμ 4 (fun z : ℝ × ℝ => uStar d - f z.1) :=
      contractionLnorm_le_const_mul (p := 4) (by norm_num) hu0 hfstm (fun z : ℝ × ℝ => hufb z.1)
        (fun z : ℝ × ℝ => le_of_eq (by rw [abs_mul, abs_of_nonneg hu0]; ring))
    have hfub : uStar d * Lnorm gμ 4 (fun z : ℝ × ℝ => uStar d - f z.1)
        = uStar d * Lnorm unitμ 4 (fun x => uStar d - f x) :=
      congrArg (fun t => uStar d * t) (factorSolutionLnorm_fst fun x => uStar d - f x)
    rw [hfub, hLfst] at h
    exact h
  have hB : Lnorm gμ 4 (fun z : ℝ × ℝ => f z.1 * (uStar d - f z.2))
      ≤ contractionM d * Lnorm unitμ 4 (fun x => f x - uStar d) := by
    have h : Lnorm gμ 4 (fun z : ℝ × ℝ => f z.1 * (uStar d - f z.2))
        ≤ contractionM d * Lnorm gμ 4 (fun z : ℝ × ℝ => uStar d - f z.2) :=
      contractionLnorm_le_const_mul (p := 4) (by norm_num) hM.le hsndm (fun z : ℝ × ℝ => hufb z.2)
        (fun z : ℝ × ℝ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (by rw [abs_of_nonneg (hnn z.1)]; exact hMb z.1) (abs_nonneg _))
    have hfub : contractionM d * Lnorm gμ 4 (fun z : ℝ × ℝ => uStar d - f z.2)
        = contractionM d * Lnorm unitμ 4 (fun x => uStar d - f x) :=
      congrArg (fun t => contractionM d * t) (factorSolutionLnorm_snd fun x => uStar d - f x)
    rw [hfub, hLfst] at h
    exact h
  have hUeq : Lnorm gμ 4 (fun z : ℝ × ℝ => contractionU W d z.1 z.2) = contractionEps W d := rfl
  rw [hcong]
  refine le_trans hm1 ?_
  rw [hUeq, hcong2]
  have := le_trans hm2 (add_le_add hA hB)
  linarith

/-! ## `eq:rank-one-reduction-bounds` -/

/-- **`eq:rank-one-reduction-bounds`**: for a solution of the nonlinear Factor equation with
`q ≥ 2^{-d}`,

`‖f - u_*‖₄ + ‖E‖₄ ≤ C(d)·ε`,  `ε = ‖W - r_*‖_{L⁴([0,1]²)}`,  `E = W - f ⊗ f`,

with the explicit constant `C(d) = factorSolutionCloseConst d`, depending only on `d`.

No smallness of `ε` is needed: the bound is linear in `ε` for every graphon `W`.  (The paper
states the same estimate under `‖W - r_*‖₄ ≤ ε`, which is how `ε` is used downstream.) -/
theorem factorSolution_closeness (hd : 2 ≤ d) (hmeas : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hMb : ∀ x, f x ≤ contractionM d) (hq : 0 < q)
    (heq : ∀ x, kernelOp W.toFun (fun y => f y ^ (d - 1)) x = q * f x)
    (hqdef : q = ∫ x, f x ^ d ∂unitμ) (hqlow : (1 : ℝ) / 2 ^ d ≤ q) :
    Lnorm unitμ 4 (fun x => f x - uStar d)
        + Lnorm gμ 4 (fun z : ℝ × ℝ => W.toFun z.1 z.2 - f z.1 * f z.2)
      ≤ factorSolutionCloseConst d * contractionEps W d := by
  have hL := factorSolution_Lnorm_sub_uStar_le hd hmeas hnn hMb hq heq hqdef hqlow
  have hE := factorSolution_Lnorm_resid_le (W := W) hd hmeas hnn hMb
  have hcoef : (0 : ℝ) ≤ 1 + uStar d + contractionM d := by
    have := uStar_nonneg hd
    have := (contractionM_pos hd).le
    linarith
  have hmul : (1 + uStar d + contractionM d) * Lnorm unitμ 4 (fun x => f x - uStar d)
      ≤ (1 + uStar d + contractionM d) * (factorSolutionK2 d * (factorSolutionDelta d * contractionEps W d)) :=
    mul_le_mul_of_nonneg_left hL hcoef
  have hfin : (1 + uStar d + contractionM d)
      * (factorSolutionK2 d * (factorSolutionDelta d * contractionEps W d))
      = (factorSolutionCloseConst d - 1) * contractionEps W d := by
    simp only [factorSolutionCloseConst]
    ring
  simp only [factorSolutionCloseConst] at hfin ⊢
  nlinarith [hL, hE, hmul, hfin]

end UpperTailOptimizers
