import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs
import UpperTailOptimizers.Preliminaries.Graphons.Basic

/-!
# The nonlinear Factor decomposition: the algebraic half (Section 5)

This file formalises the **algebraic consequences** of `lem:localization-rank-one`
of `paper/sections/singular.tex`.  That lemma produces, for a graphon `W` close to the constant
kernel at the exceptional density `r_*`, a nonnegative factor `f` with

`T_W(f^{d-1}) = q f`,   `∫ E(x,y) f(y)^{d-1} dy = 0` for a.e. `x`
`eq:rank-one-orthogonality`,

where `q = ∫ f^d`, `A = f ⊗ f` and `E = W - A`.  The **existence** of `(f, q, E)` is a
genuinely infinite-dimensional argument (in the paper a variational problem in `L^{d/(d-1)}`;
in Lean the normalised contraction of `SingularEndpoint/LocalizationRankOne/FactorContraction.lean`) and is *not*
formalised here.  Instead
the decomposition is transcribed as a structure `FactorDecomp d W` whose fields are the
lemma's conclusions — exactly the `📐` discipline used by `KKTFamily` — and this file
proves what follows from it by Fubini and the binomial theorem.

The one thing everything rests on is that the orthogonality relation kills the linear term
of the exact binomial expansion of `∫ W^d`, so that the moment error `∫W^d - q²` (bounded in the
proof of `lem:localization-rank-one`) starts at order two in `E`.  That is `linear_term_zero`,
and `Wmoment_eq` is the expansion itself.

All functions in sight are bounded and measurable on a probability space (`W` takes values
in `[0,1]` and `0 ≤ f ≤ 2`, so `|E| ≤ 5`), so every integrability side condition is a
uniform bound; `integrable_of_abs_le` is the only tool needed.

## Contents

* `FactorDecomp` — the conclusion of `lem:localization-rank-one` as data: the factor
  `f`, its measurability, the bounds `0 ≤ f ≤ 2`, and the orthogonality field `ortho`,
  which is the second half of `eq:rank-one-orthogonality`;
* `FactorDecomp.qVal`, `FactorDecomp.rankOne`, `FactorDecomp.resid` — the rank-one moment
  `q = ∫ f^d`, the rank-one part `A = f ⊗ f` and the residual `E = W - A`;
* `FactorDecomp.abs_f_le`, `abs_rankOne_le`, `abs_resid_le` and the `integrable_*` family —
  the uniform bounds and the integrability infrastructure they give;
* `FactorDecomp.factor_eq` — the first half of `eq:rank-one-orthogonality`,
  `T_W(f^{d-1}) = q f`;
* `FactorDecomp.rankOne_moment` — `∫∫ A^d = q^2`;
* `FactorDecomp.linear_term_zero` — `∫∫ A^{d-1} E = 0`, the crux;
* `FactorDecomp.Wmoment_eq` — the binomial expansion from the proof of
  `lem:localization-rank-one`, `∫ W^d = q^2 + ∑_{k < d-1} binom(d,k) ∫∫ A^k E^{d-k}`;
* `FactorDecomp.qVal_mul_f_le` — the elementary half of
  `eq:rank-one-orthogonality`, `q f(x) ≤ ∫ f^{d-1}`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ} {W : Graphon}

/-! ## Elementary bounded-function tools -/

/-- Powers respect a uniform bound in absolute value. -/
private theorem abs_pow_le' {a A : ℝ} (h : |a| ≤ A) (k : ℕ) : |a ^ k| ≤ A ^ k := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg a) h k

/-- Products respect uniform bounds in absolute value. -/
private theorem abs_mul_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) (le_trans (abs_nonneg a) ha)

/-- `y ↦ W(x,y)` is measurable for each fixed `x`: the slice needed for the inner integral
of `eq:rank-one-orthogonality`. -/
theorem measurable_toFun_right (W : Graphon) (x : ℝ) : Measurable (fun y => W.toFun x y) :=
  W.meas'.of_uncurry_left

/-! ## The decomposition as data -/

/-- The conclusion of `lem:localization-rank-one`, transcribed as data.

Given a graphon `W`, a `FactorDecomp d W` is a nonnegative bounded measurable factor `f`
satisfying the second identity of `eq:rank-one-orthogonality`,
`∫ (W(x,y) - f(x)f(y)) f(y)^{d-1} dy = 0` for a.e. `x`.

The bound `f ≤ 2` is a harmless normalisation: `eq:rank-one-orthogonality` gives
`f ≤ q^{-1/d}`, and along the family `q → u_*^d`, so any fixed uniform bound will do; `2`
is chosen because it makes the residual bound `|E| ≤ 5` explicit.  Constructing a term of
this structure is the infinite-dimensional part of the lemma and is not attempted here; it is
`exists_factorDecomp` (`SingularEndpoint/LocalizationRankOne/FactorMain.lean`), built by the contraction iteration of
`SingularEndpoint/LocalizationRankOne/FactorContraction.lean`, `SingularEndpoint/LocalizationRankOne/FactorFix.lean` and `SingularEndpoint/LocalizationRankOne/FactorSolution.lean`. -/
structure FactorDecomp (d : ℕ) (W : Graphon) where
  /-- The rank-one factor `f` of `W ≈ f ⊗ f`. -/
  f : ℝ → ℝ
  /-- `f` is measurable. -/
  meas_f : Measurable f
  /-- `f` is nonnegative, as produced by the variational construction. -/
  f_nonneg : ∀ x, 0 ≤ f x
  /-- `f` is uniformly bounded (normalisation; see `eq:rank-one-orthogonality`). -/
  f_bdd : ∀ x, f x ≤ 2
  /-- The orthogonality relation `∫ E(x,y) f(y)^{d-1} dy = 0`, the second half of
  `eq:rank-one-orthogonality`. -/
  ortho : ∀ᵐ x ∂unitμ, ∫ y, (W.toFun x y - f x * f y) * f y ^ (d - 1) ∂unitμ = 0

namespace FactorDecomp

variable (P : FactorDecomp d W)

/-- The **rank-one moment** `q = ∫ f^d` of `lem:localization-rank-one`. -/
noncomputable def qVal : ℝ := ∫ x, P.f x ^ d ∂unitμ

/-- The **rank-one part** `A = f ⊗ f`. -/
def rankOne (x y : ℝ) : ℝ := P.f x * P.f y

/-- The **residual** `E = W - f ⊗ f` of `lem:localization-rank-one`. -/
def resid (x y : ℝ) : ℝ := W.toFun x y - P.f x * P.f y

/-- `W = A + E` pointwise: the splitting the binomial expansion is applied to. -/
theorem rankOne_add_resid (x y : ℝ) : P.rankOne x y + P.resid x y = W.toFun x y := by
  simp only [rankOne, resid]; ring

/-! ## Uniform bounds -/

theorem abs_f_le (x : ℝ) : |P.f x| ≤ 2 :=
  abs_le.mpr ⟨by linarith [P.f_nonneg x], P.f_bdd x⟩

theorem rankOne_nonneg (x y : ℝ) : 0 ≤ P.rankOne x y :=
  mul_nonneg (P.f_nonneg x) (P.f_nonneg y)

theorem abs_rankOne_le (x y : ℝ) : |P.rankOne x y| ≤ 4 := by
  have := abs_mul_le' (P.abs_f_le x) (P.abs_f_le y)
  simpa [rankOne] using this.trans_eq (by norm_num)

theorem abs_resid_le (x y : ℝ) : |P.resid x y| ≤ 5 := by
  have h1 : |W.toFun x y| ≤ 1 :=
    abs_le.mpr ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩
  have h2 : |P.f x * P.f y| ≤ 4 := P.abs_rankOne_le x y
  calc |P.resid x y| = |W.toFun x y - P.f x * P.f y| := rfl
    _ ≤ |W.toFun x y| + |P.f x * P.f y| := abs_sub _ _
    _ ≤ 5 := by linarith

/-! ## Measurability and integrability -/

theorem measurable_f_pow (k : ℕ) : Measurable (fun y => P.f y ^ k) := P.meas_f.pow_const k

theorem measurable_rankOne : Measurable (fun z : ℝ × ℝ => P.rankOne z.1 z.2) :=
  (P.meas_f.comp measurable_fst).mul (P.meas_f.comp measurable_snd)

theorem measurable_resid : Measurable (fun z : ℝ × ℝ => P.resid z.1 z.2) :=
  W.measurable_uncurry.sub P.measurable_rankOne

theorem measurable_resid_right (x : ℝ) : Measurable (fun y => P.resid x y) :=
  (measurable_toFun_right W x).sub (measurable_const.mul P.meas_f)

theorem integrable_f_pow (k : ℕ) : Integrable (fun y => P.f y ^ k) unitμ :=
  integrable_of_abs_le (P.measurable_f_pow k) (2 ^ k) fun y => abs_pow_le' (P.abs_f_le y) k

theorem integrable_W_mul_f_pow (x : ℝ) (k : ℕ) :
    Integrable (fun y => W.toFun x y * P.f y ^ k) unitμ := by
  refine integrable_of_abs_le ((measurable_toFun_right W x).mul (P.measurable_f_pow k)) (1 * 2 ^ k)
    fun y => abs_mul_le' ?_ (abs_pow_le' (P.abs_f_le y) k)
  exact abs_le.mpr ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩

theorem integrable_resid_mul_f_pow (x : ℝ) (k : ℕ) :
    Integrable (fun y => P.resid x y * P.f y ^ k) unitμ :=
  integrable_of_abs_le ((P.measurable_resid_right x).mul (P.measurable_f_pow k)) (5 * 2 ^ k)
    fun y => abs_mul_le' (P.abs_resid_le x y) (abs_pow_le' (P.abs_f_le y) k)

/-- The generic term of the binomial expansion is integrable on `[0,1]²`. -/
theorem integrable_rankOne_pow_mul_resid_pow (k m : ℕ) :
    Integrable (fun z : ℝ × ℝ => P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ m) gμ :=
  integrable_of_abs_le
    ((P.measurable_rankOne.pow_const k).mul (P.measurable_resid.pow_const m)) (4 ^ k * 5 ^ m)
    fun z => abs_mul_le' (abs_pow_le' (P.abs_rankOne_le z.1 z.2) k)
      (abs_pow_le' (P.abs_resid_le z.1 z.2) m)

/-! ## The Factor equation -/

/-- **The first half of `eq:rank-one-orthogonality`**: `T_W(f^{d-1}) = q f`, i.e.
`∫ W(x,y) f(y)^{d-1} dy = q f(x)` for a.e. `x`.

This is the orthogonality field `ortho` with the subtracted term evaluated: it is
`f(x) ∫ f(y) f(y)^{d-1} dy = f(x) ∫ f^d = q f(x)`, using `1 ≤ d` to collapse
`f · f^{d-1}` to `f^d`. -/
theorem factor_eq (hd : 1 ≤ d) :
    ∀ᵐ x ∂unitμ, ∫ y, W.toFun x y * P.f y ^ (d - 1) ∂unitμ = P.qVal * P.f x := by
  filter_upwards [P.ortho] with x hx
  have hy : ∀ y : ℝ, P.f y * P.f y ^ (d - 1) = P.f y ^ d := by
    intro y
    have hde : d - 1 + 1 = d := Nat.succ_pred_eq_of_pos hd
    calc P.f y * P.f y ^ (d - 1) = P.f y ^ (d - 1 + 1) := by ring
      _ = P.f y ^ d := by rw [hde]
  have hpt : ∀ y : ℝ, (W.toFun x y - P.f x * P.f y) * P.f y ^ (d - 1)
      = W.toFun x y * P.f y ^ (d - 1) - P.f x * P.f y ^ d := by
    intro y
    calc (W.toFun x y - P.f x * P.f y) * P.f y ^ (d - 1)
        = W.toFun x y * P.f y ^ (d - 1) - P.f x * (P.f y * P.f y ^ (d - 1)) := by ring
      _ = W.toFun x y * P.f y ^ (d - 1) - P.f x * P.f y ^ d := by rw [hy]
  have hx' : ∫ y, (W.toFun x y * P.f y ^ (d - 1) - P.f x * P.f y ^ d) ∂unitμ = 0 :=
    (integral_congr_ae (Filter.Eventually.of_forall hpt)).symm.trans hx
  rw [integral_sub (P.integrable_W_mul_f_pow x (d - 1)) ((P.integrable_f_pow d).const_mul _),
    integral_const_mul] at hx'
  simp only [qVal]
  linarith

/-! ## The rank-one moment and the vanishing linear term -/

/-- `∫∫ A^d = q^2` for the rank-one part `A = f ⊗ f`: the leading term of
`eq:rank-one-reduction-bounds`. -/
theorem rankOne_moment : ∫ z, P.rankOne z.1 z.2 ^ d ∂gμ = P.qVal ^ 2 := by
  have h : ∀ z : ℝ × ℝ, P.rankOne z.1 z.2 ^ d = P.f z.1 ^ d * P.f z.2 ^ d := by
    intro z; simp [rankOne, mul_pow]
  have e1 : ∫ z, P.rankOne z.1 z.2 ^ d ∂gμ = ∫ z : ℝ × ℝ, P.f z.1 ^ d * P.f z.2 ^ d ∂gμ :=
    integral_congr_ae (Filter.Eventually.of_forall h)
  have e2 := integral_prod_mul (μ := unitμ) (ν := unitμ)
    (fun x : ℝ => P.f x ^ d) (fun y : ℝ => P.f y ^ d)
  rw [e1, show gμ = unitμ.prod unitμ from rfl, e2]
  simp only [qVal]
  ring

/-- **The crux of `lem:localization-rank-one`**: the linear term of the binomial
expansion vanishes, `∫∫ A^{d-1} E = 0`.

By Fubini the double integral is `∫ f(x)^{d-1} (∫ E(x,y) f(y)^{d-1} dy) dx`, and the inner
integral is a.e. zero by the orthogonality field.  This is what makes
`eq:rank-one-reduction-bounds` start at order two in `E`. -/
theorem linear_term_zero (_hd : 1 ≤ d) :
    ∫ z, P.rankOne z.1 z.2 ^ (d - 1) * P.resid z.1 z.2 ∂gμ = 0 := by
  have hfun : (fun z : ℝ × ℝ => P.rankOne z.1 z.2 ^ (d - 1) * P.resid z.1 z.2)
      = fun z : ℝ × ℝ => P.f z.1 ^ (d - 1) * (P.resid z.1 z.2 * P.f z.2 ^ (d - 1)) := by
    funext z
    simp only [rankOne, mul_pow]
    ring
  have hint : Integrable
      (fun z : ℝ × ℝ => P.f z.1 ^ (d - 1) * (P.resid z.1 z.2 * P.f z.2 ^ (d - 1)))
      (unitμ.prod unitμ) := by
    have := P.integrable_rankOne_pow_mul_resid_pow (d - 1) 1
    simp only [pow_one] at this
    rw [hfun] at this
    exact this
  rw [hfun, show gμ = unitμ.prod unitμ from rfl, integral_prod _ hint]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [P.ortho] with x hx
  have hx' : ∫ y, P.resid x y * P.f y ^ (d - 1) ∂unitμ = 0 := hx
  simp only [integral_const_mul, hx', mul_zero, Pi.zero_apply]

/-! ## The expansion `eq:rank-one-reduction-bounds` -/

/-- **`eq:rank-one-reduction-bounds`**: the exact binomial expansion of the `d`-th moment about
the rank-one part,

`∫ W^d = q^2 + ∑_{k < d-1} binom(d,k) ∫∫ A^k E^{d-k}`.

The two top terms of the binomial sum are the ones peeled off: `k = d` contributes
`∫∫ A^d = q^2` (`rankOne_moment`), and `k = d-1` contributes `d ∫∫ A^{d-1} E = 0`
(`linear_term_zero`).  The remaining sum is quadratic in `E`, which is the point of the
whole lemma. -/
theorem Wmoment_eq (hd : 1 ≤ d) :
    W.Wmoment d = P.qVal ^ 2 +
      ∑ k ∈ Finset.range (d - 1), (d.choose k : ℝ) *
        ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (d - k) ∂gμ := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  set b : ℕ → ℝ := fun k =>
    ∫ z, P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (m + 1 - k) ∂gμ with hb
  -- the pointwise binomial identity
  have hpt : ∀ z : ℝ × ℝ, W.toFun z.1 z.2 ^ (m + 1)
      = ∑ k ∈ Finset.range (m + 2),
        P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (m + 1 - k) * ((m + 1).choose k : ℝ) := by
    intro z
    rw [← P.rankOne_add_resid z.1 z.2, add_pow]
  have e0 : W.Wmoment (m + 1) = ∫ z, (∑ k ∈ Finset.range (m + 2),
      P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (m + 1 - k) * ((m + 1).choose k : ℝ)) ∂gμ := by
    rw [Graphon.Wmoment]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have e1 : ∫ z, (∑ k ∈ Finset.range (m + 2),
      P.rankOne z.1 z.2 ^ k * P.resid z.1 z.2 ^ (m + 1 - k) * ((m + 1).choose k : ℝ)) ∂gμ
      = ∑ k ∈ Finset.range (m + 2), ((m + 1).choose k : ℝ) * b k := by
    rw [integral_finsetSum _ (fun k _ =>
      ((P.integrable_rankOne_pow_mul_resid_pow k (m + 1 - k)).mul_const _))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_mul_const, hb]
    ring
  -- peel the top two terms
  have hbtop : b (m + 1) = P.qVal ^ 2 := by
    have : b (m + 1) = ∫ z, P.rankOne z.1 z.2 ^ (m + 1) ∂gμ := by
      rw [hb]; simp
    rw [this, P.rankOne_moment]
  have hbnext : b m = 0 := by
    have hbm : b m = ∫ z, P.rankOne z.1 z.2 ^ (m + 1 - 1) * P.resid z.1 z.2 ∂gμ := by
      rw [hb]
      norm_num
    rw [hbm, P.linear_term_zero hd]
  rw [e0, e1, Finset.sum_range_succ, Finset.sum_range_succ, hbtop, hbnext]
  simp only [Nat.add_sub_cancel, Nat.choose_self, Nat.cast_one, one_mul, mul_zero, add_zero]
  ring

/-! ## The pointwise bound -/

/-- The elementary half of `eq:rank-one-orthogonality`:
`q f(x) = ∫ W(x,y) f(y)^{d-1} dy ≤ ∫ f^{d-1}` for a.e. `x`, because `W ≤ 1` and `f ≥ 0`.

(The second half of the display, `∫ f^{d-1} ≤ q^{(d-1)/d}`, is Hölder's inequality and is
not needed by the algebraic consequences proved here.) -/
theorem qVal_mul_f_le (hd : 1 ≤ d) :
    ∀ᵐ x ∂unitμ, P.qVal * P.f x ≤ ∫ y, P.f y ^ (d - 1) ∂unitμ := by
  filter_upwards [P.factor_eq hd] with x hx
  rw [← hx]
  refine integral_mono (P.integrable_W_mul_f_pow x (d - 1)) (P.integrable_f_pow (d - 1))
    fun y => ?_
  have hnn : 0 ≤ P.f y ^ (d - 1) := pow_nonneg (P.f_nonneg y) _
  nlinarith [W.le_one' x y, W.nonneg' x y]

end FactorDecomp

end SingularEndpoint

end UpperTailOptimizers
