import UpperTailOptimizers.Preliminaries.Graphons.Basic

/-!
# The kernel operator `T_K` and its `L⁴` bound (Section 5)

`paper/sections/singular.tex` introduces, just before `lem:localization-rank-one`, the kernel
operator

`(T_K g)(x) := ∫₀¹ K(x,y) g(y) dy`,

and the proof of that lemma bounds it by Hölder's inequality in two forms:
`‖(T_W - T_{S_n})g‖_d ≤ ‖W - S_n‖_d ‖g‖_{d'}`, `d' = d/(d-1)`, to show that
`T_W : L^{d'} → L^d` is compact, and `‖T_{W-r_*}(f^{d-1})‖₄ ≤ ‖W - r_*‖₄ ‖f^{d-1}‖_{4/3}` in
the factor bounds.  This file formalises the second form, for a bounded measurable kernel;
its exponent pair is also the one the normalised contraction construction of the
**existence** half needs,

`‖T_K g‖₄ ≤ ‖K‖_{L⁴([0,1]²)} · ‖g‖_{4/3}`   (`Lnorm_kernelOp_le`),

together with the elementary scalar estimates the same construction needs: the Lipschitz bound
for `t ↦ t^{d-1}` on `[0,M]`, the probability-space comparison `‖g‖_{4/3} ≤ ‖g‖₄`, and the
Jensen/Bernoulli lower bound `∫ φ^n ≥ 1` for a nonnegative `φ` of unit mass (used with
`n = d-1` to keep the normalising denominator of the construction bounded below, and with
`n = d` to bound below the moment `q = ∫ f^d` of the rescaled factor, which gives the
pointwise clause `0 ≤ f ≤ 2` of `eq:rank-one-orthogonality` through `f ≤ q^{-1/d}`).

**What is not here.**  The contraction itself, and hence the existence half of
`lem:localization-rank-one`, is *not* proved here; neither is the uniqueness of the factor
that the Lean construction adds (`factorMain_unique`), the bounds
`eq:rank-one-reduction-bounds`, or the coercivity estimate of
`SingularEndpoint/LocalizationRankOne/FactorStability.lean`.  This file is the operator-theoretic foundation
those need.  `SingularEndpoint/LocalizationRankOne/Factor.lean` carries the algebraic consequences of the decomposition,
transcribed as `FactorDecomp`; nothing here depends on that structure, and in particular
nothing here assumes any closeness bound.

**Design decision: raw functions, not Mathlib `Lp`.**  Everything is stated with plain
functions `ℝ → ℝ` and `MeasureTheory.integral`, matching `SingularEndpoint/LocalizationRankOne/Factor.lean` and the rest of
the `SingularEndpoint/` layer.  The `L^p` quantity is the *function* `Lnorm μ p h = (∫ |h|^p)^{1/p}`,
not an element of a quotient space.  Two reasons: (i) every function in the contraction construction
carries an explicit uniform bound (graphon kernels are `[0,1]`-valued and the iterates are
bounded by an explicit `M`), so all integrability side conditions are discharged by the
`integrable_of_abs_le` idiom rather than by `MemLp` bookkeeping; (ii) the orthogonality field of
`FactorDecomp` is a genuine pointwise a.e. statement about a chosen representative, which does
not live in an a.e.-class quotient.  Mathlib `MemLp` is used only *inside* proofs, as the input
format of Hölder's inequality.

## Contents

* `Lnorm` — `(∫ |h|^p ∂μ)^{1/p}` for a raw function, with `integral_abs_rpow_nonneg`,
  `Lnorm_nonneg`, `Lnorm_rpow` (`‖h‖_p^p = ∫|h|^p`) and `Lnorm_le_one`;
* `kernelOp` — `(T_K g)(x) = ∫ K(x,y) g(y) dy`, with `measurable_kernelOp` and the sup bound
  `abs_kernelOp_le`;
* `abs_kernelOp_le_Lnorm` — pointwise Hölder in `y` at a fixed `x`;
* `integral_abs_kernelOp_rpow_le` — the `4`-th power form of the operator bound (Tonelli);
* `Lnorm_kernelOp_le` — **the `L⁴` operator bound** `‖T_K g‖₄ ≤ ‖K‖₄ ‖g‖_{4/3}`;
* `Lnorm_kernelOp_graphon_le` — its graphon specialisation `‖T_W g‖₄ ≤ ‖g‖_{4/3}`;
* `abs_pow_sub_pow_le_box`, `abs_pow_sub_pow_le_deg` — `|a^{d-1} - b^{d-1}| ≤ (d-1)M^{d-2}|a-b|`
  on `[0,M]`.  The name carries `_box` because `NonexceptionalEndpoint/QuadraticGrowth/PowBounds.lean` has an
  unrelated `abs_pow_sub_pow_le`, the `[0,1]` bound with constant `k`;
* `Lnorm_43_le_Lnorm_4` — `‖g‖_{4/3} ≤ ‖g‖₄` on the probability space `unitμ`;
* `one_le_integral_pow`, `one_le_integral_pow_sub_one` — `∫ φ^n ≥ 1` when `φ ≥ 0` and
  `∫ φ = 1`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

/-! ## The `L^p` functional on raw functions -/

/-- `‖h‖_{L^p(μ)} = (∫ |h|^p)^{1/p}`, as a raw function of `h` (no `Lp` quotient).  The exponent
`p` is a real number and the powers are `Real.rpow`, so that `p = 4/3` is allowed. -/
noncomputable def Lnorm {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : ℝ)
    (h : α → ℝ) : ℝ :=
  (∫ x, |h x| ^ p ∂μ) ^ (1 / p)

/-- The integrand `|h|^p` is nonnegative, hence so is its integral. -/
theorem integral_abs_rpow_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : ℝ)
    (h : α → ℝ) : 0 ≤ ∫ x, |h x| ^ p ∂μ :=
  integral_nonneg fun _x => Real.rpow_nonneg (abs_nonneg _) _

/-- `‖h‖_{L^p(μ)} ≥ 0`. -/
theorem Lnorm_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : ℝ) (h : α → ℝ) :
    0 ≤ Lnorm μ p h :=
  Real.rpow_nonneg (integral_abs_rpow_nonneg μ p h) _

/-- `‖h‖_{L^p(μ)}^p = ∫ |h|^p`: the form in which the `L^p` functional is fed to Hölder. -/
theorem Lnorm_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ} (hp : p ≠ 0)
    (h : α → ℝ) : Lnorm μ p h ^ p = ∫ x, |h x| ^ p ∂μ := by
  rw [Lnorm, ← Real.rpow_mul (integral_abs_rpow_nonneg μ p h), one_div, inv_mul_cancel₀ hp,
    Real.rpow_one]

/-- On a probability space a function bounded by `1` has `L^p` functional at most `1`
(`p ≥ 0`). -/
theorem Lnorm_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 0 ≤ p) {h : α → ℝ} (hm : Measurable h) (hb : ∀ x, |h x| ≤ 1) :
    Lnorm μ p h ≤ 1 := by
  have hmp : Measurable fun x => |h x| ^ p :=
    (Real.continuous_rpow_const hp).measurable.comp hm.abs
  have hint : Integrable (fun x => |h x| ^ p) μ :=
    integrable_of_abs_le hmp 1 fun x => by
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_one (abs_nonneg _) (hb x) hp
  have hle : ∫ x, |h x| ^ p ∂μ ≤ 1 := by
    calc ∫ x, |h x| ^ p ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ :=
          integral_mono hint (integrable_const 1) fun x =>
            Real.rpow_le_one (abs_nonneg _) (hb x) hp
      _ = 1 := by simp
  exact Real.rpow_le_one (integral_abs_rpow_nonneg μ p h) hle (div_nonneg zero_le_one hp)

/-! ## The kernel operator -/

/-- The kernel operator `(T_K g)(x) = ∫₀¹ K(x,y) g(y) dy` of `paper/sections/singular.tex`. -/
noncomputable def kernelOp (K : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, K x y * g y ∂unitμ

variable {K : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {CK Cg : ℝ}

/-- `T_K g` is measurable: this is measurability of a partial Bochner integral,
`MeasureTheory.StronglyMeasurable.integral_prod_right'`. -/
theorem measurable_kernelOp (hK : Measurable (Function.uncurry K)) (hg : Measurable g) :
    Measurable (kernelOp K g) := by
  have hm : Measurable fun z : ℝ × ℝ => K z.1 z.2 * g z.2 := hK.mul (hg.comp measurable_snd)
  have hsm : StronglyMeasurable fun x => ∫ y, K x y * g y ∂unitμ :=
    hm.stronglyMeasurable.integral_prod_right'
  exact hsm.measurable

/-- The crude sup bound `|(T_K g)(x)| ≤ C_K C_g`, from `|K| ≤ C_K`, `|g| ≤ C_g` and the fact
that `unitμ` is a probability measure. -/
theorem abs_kernelOp_le (hK : Measurable (Function.uncurry K)) (hg : Measurable g)
    (hKb : ∀ x y, |K x y| ≤ CK) (hgb : ∀ y, |g y| ≤ Cg) (x : ℝ) :
    |kernelOp K g x| ≤ CK * Cg := by
  have hCK : 0 ≤ CK := (abs_nonneg _).trans (hKb x x)
  have hptw : ∀ y, |K x y * g y| ≤ CK * Cg := fun y => by
    rw [abs_mul]; exact mul_le_mul (hKb x y) (hgb y) (abs_nonneg _) hCK
  have hint : Integrable (fun y => K x y * g y) unitμ :=
    integrable_of_abs_le (hK.of_uncurry_left.mul hg) (CK * Cg) hptw
  calc |kernelOp K g x| ≤ ∫ y, |K x y * g y| ∂unitμ := abs_integral_le_integral_abs
    _ ≤ ∫ _y, CK * Cg ∂unitμ := integral_mono hint.abs (integrable_const _) hptw
    _ = CK * Cg := by simp

/-- **Pointwise Hölder in `y` at a fixed `x`**, with the conjugate pair `(4, 4/3)`:
`|(T_K g)(x)| ≤ ‖K(x,·)‖₄ ‖g‖_{4/3}`. -/
theorem abs_kernelOp_le_Lnorm (hK : Measurable (Function.uncurry K)) (hg : Measurable g)
    (hKb : ∀ x y, |K x y| ≤ CK) (hgb : ∀ y, |g y| ≤ Cg) (x : ℝ) :
    |kernelOp K g x| ≤ Lnorm unitμ 4 (fun y => K x y) * Lnorm unitμ (4 / 3) g := by
  have hpq : Real.HolderConjugate 4 (4 / 3) := ⟨by norm_num, by norm_num, by norm_num⟩
  have hf : MemLp (fun y => |K x y|) (ENNReal.ofReal 4) unitμ :=
    MemLp.of_bound (hK.of_uncurry_left.abs.aestronglyMeasurable) CK
      (Filter.Eventually.of_forall fun y => by simpa using hKb x y)
  have hgL : MemLp (fun y => |g y|) (ENNReal.ofReal (4 / 3)) unitμ :=
    MemLp.of_bound hg.abs.aestronglyMeasurable Cg
      (Filter.Eventually.of_forall fun y => by simpa using hgb y)
  have hol := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun y => abs_nonneg (K x y))
    (Filter.Eventually.of_forall fun y => abs_nonneg (g y)) hf hgL
  calc |kernelOp K g x| ≤ ∫ y, |K x y * g y| ∂unitμ := abs_integral_le_integral_abs
    _ = ∫ y, |K x y| * |g y| ∂unitμ := by simp_rw [abs_mul]
    _ ≤ Lnorm unitμ 4 (fun y => K x y) * Lnorm unitμ (4 / 3) g := hol

/-- The `4`-th power form of the operator bound,
`∫ |T_K g|⁴ ≤ (∫∫ |K|⁴) ‖g‖_{4/3}⁴`.

This is the pointwise Hölder bound raised to the fourth power and integrated in `x`; the
`x`-integral of the row mass `∫ |K(x,·)|⁴` is the double integral by Fubini
(`MeasureTheory.integral_prod`, legitimate here because `|K|⁴` is bounded). -/
theorem integral_abs_kernelOp_rpow_le (hK : Measurable (Function.uncurry K))
    (hg : Measurable g) (hKb : ∀ x y, |K x y| ≤ CK) (hgb : ∀ y, |g y| ≤ Cg) :
    ∫ x, |kernelOp K g x| ^ (4 : ℝ) ∂unitμ
      ≤ (∫ z, |K z.1 z.2| ^ (4 : ℝ) ∂gμ) * Lnorm unitμ (4 / 3) g ^ (4 : ℝ) := by
  have hNnn : 0 ≤ Lnorm unitμ (4 / 3) g := Lnorm_nonneg _ _ _
  -- (a) the pointwise bound, raised to the fourth power
  have hpt : ∀ x, |kernelOp K g x| ^ (4 : ℝ)
      ≤ (∫ y, |K x y| ^ (4 : ℝ) ∂unitμ) * Lnorm unitμ (4 / 3) g ^ (4 : ℝ) := by
    intro x
    have h1 := abs_kernelOp_le_Lnorm hK hg hKb hgb x
    have h2 := Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num : (0 : ℝ) ≤ 4)
    rwa [Real.mul_rpow (Lnorm_nonneg _ _ _) hNnn,
      Lnorm_rpow (by norm_num : (4 : ℝ) ≠ 0)] at h2
  -- (b) integrability of the two sides
  have hmeasT : Measurable (kernelOp K g) := measurable_kernelOp hK hg
  have hLmeas : Measurable fun x => |kernelOp K g x| ^ (4 : ℝ) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4)).measurable.comp hmeasT.abs
  have hLint : Integrable (fun x => |kernelOp K g x| ^ (4 : ℝ)) unitμ :=
    integrable_of_abs_le hLmeas ((CK * Cg) ^ (4 : ℝ)) fun x => by
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (abs_kernelOp_le hK hg hKb hgb x) (by norm_num)
  have hKmeas : Measurable fun z : ℝ × ℝ => |K z.1 z.2| ^ (4 : ℝ) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4)).measurable.comp hK.abs
  have hsq : Integrable (fun z : ℝ × ℝ => |K z.1 z.2| ^ (4 : ℝ)) (unitμ.prod unitμ) :=
    integrable_of_abs_le hKmeas (CK ^ (4 : ℝ)) fun z => by
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hKb z.1 z.2) (by norm_num)
  have hrow : Integrable (fun x => ∫ y, |K x y| ^ (4 : ℝ) ∂unitμ) unitμ := hsq.integral_prod_left
  -- (c) integrate in `x` and apply Fubini to the row masses
  have hstep := integral_mono hLint (hrow.mul_const _) hpt
  rw [integral_mul_const] at hstep
  have hfub : ∫ x, (∫ y, |K x y| ^ (4 : ℝ) ∂unitμ) ∂unitμ = ∫ z, |K z.1 z.2| ^ (4 : ℝ) ∂gμ := by
    rw [show gμ = unitμ.prod unitμ from rfl, integral_prod _ hsq]
  rwa [hfub] at hstep

/-- **Target 1**: the `L⁴` bound for the kernel operator,

`‖T_K g‖₄ ≤ ‖K‖_{L⁴([0,1]²)} · ‖g‖_{4/3}`,

for a bounded measurable kernel `K` and a bounded measurable `g`.  This is the mapping property
the Lean's normalised contraction construction of the decomposition in
`lem:localization-rank-one` runs on; the paper's proof of that lemma uses it in the form
`‖T_{W-r_*}(f^{d-1})‖₄ ≤ ‖W - r_*‖₄ ‖f^{d-1}‖_{4/3}`. -/
theorem Lnorm_kernelOp_le (hK : Measurable (Function.uncurry K)) (hg : Measurable g)
    (hKb : ∀ x y, |K x y| ≤ CK) (hgb : ∀ y, |g y| ≤ Cg) :
    Lnorm unitμ 4 (kernelOp K g)
      ≤ Lnorm gμ 4 (fun z : ℝ × ℝ => K z.1 z.2) * Lnorm unitμ (4 / 3) g := by
  have hNnn : 0 ≤ Lnorm unitμ (4 / 3) g := Lnorm_nonneg _ _ _
  have hpow := integral_abs_kernelOp_rpow_le hK hg hKb hgb
  have hmono := Real.rpow_le_rpow (integral_abs_rpow_nonneg unitμ 4 (kernelOp K g)) hpow
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [Real.mul_rpow (integral_abs_rpow_nonneg gμ 4 fun z : ℝ × ℝ => K z.1 z.2)
      (Real.rpow_nonneg hNnn _), ← Real.rpow_mul hNnn,
    show (4 : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one] at hmono
  exact hmono

/-- The graphon specialisation: since `‖W‖_{L⁴([0,1]²)} ≤ 1` for a `[0,1]`-valued kernel,
`T_W` is a contraction from `L^{4/3}` to `L⁴`. -/
theorem Lnorm_kernelOp_graphon_le (W : Graphon) (hg : Measurable g) (hgb : ∀ y, |g y| ≤ Cg) :
    Lnorm unitμ 4 (kernelOp W.toFun g) ≤ Lnorm unitμ (4 / 3) g := by
  have hKb : ∀ x y, |W.toFun x y| ≤ 1 := fun x y =>
    abs_le.mpr ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩
  have hb : Lnorm gμ 4 (fun z : ℝ × ℝ => W.toFun z.1 z.2) ≤ 1 :=
    Lnorm_le_one (by norm_num) W.measurable_uncurry fun z => hKb z.1 z.2
  exact (Lnorm_kernelOp_le W.meas' hg hKb hgb).trans
    (mul_le_of_le_one_left (Lnorm_nonneg _ _ _) hb)

/-! ## Elementary power estimates

The three scalar inputs of the contraction construction.  None of them involves the kernel operator.
-/

/-- The Lipschitz estimate for `t ↦ t^n` on the box `[0,M]`:
`|a^n - b^n| ≤ n M^{n-1} |a - b|`.

Not to be confused with `UpperTailOptimizers.abs_pow_sub_pow_le`
(`NonexceptionalEndpoint/QuadraticGrowth/PowBounds.lean`), the `[0,1]` bound with the smaller constant `n`; the two are
visible together in a dozen modules, whence the `_box` suffix here.

The proof is the factorisation `a^n - b^n = (∑_{i<n} a^i b^{n-1-i})(a - b)` together with the
termwise bound `a^i b^{n-1-i} ≤ M^{n-1}` (note `i + (n-1-i) = n-1` for `i < n`, which is where
the `ℕ`-subtraction is discharged). -/
theorem abs_pow_sub_pow_le_box {M a b : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) (hb : 0 ≤ b) (hbM : b ≤ M)
    (n : ℕ) : |a ^ n - b ^ n| ≤ (n : ℝ) * M ^ (n - 1) * |a - b| := by
  have hM : 0 ≤ M := ha.trans haM
  have hterm : ∀ i ∈ Finset.range n, |a ^ i * b ^ (n - 1 - i)| ≤ M ^ (n - 1) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have h1 : a ^ i * b ^ (n - 1 - i) ≤ M ^ i * M ^ (n - 1 - i) :=
      mul_le_mul (pow_le_pow_left₀ ha haM i) (pow_le_pow_left₀ hb hbM _)
        (pow_nonneg hb _) (pow_nonneg hM _)
    have h2 : M ^ i * M ^ (n - 1 - i) = M ^ (n - 1) := by
      rw [← pow_add, show i + (n - 1 - i) = n - 1 from by omega]
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))]
    exact h2 ▸ h1
  have hfac : a ^ n - b ^ n = (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) * (a - b) :=
    (geom_sum₂_mul a b n).symm
  rw [hfac, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc |∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)|
      ≤ ∑ i ∈ Finset.range n, |a ^ i * b ^ (n - 1 - i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, M ^ (n - 1) := Finset.sum_le_sum hterm
    _ = (n : ℝ) * M ^ (n - 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The degree-flavoured form used by the contraction construction:
`|a^{d-1} - b^{d-1}| ≤ (d-1) M^{d-2} |a - b|` on `[0,M]`, for `2 ≤ d`.

The hypothesis `2 ≤ d` is what makes `M^{d-2}` the honest exponent: for `d < 2` the `ℕ`-truncated
`d - 2` would be `0` and the bound would be false in general. -/
theorem abs_pow_sub_pow_le_deg {d : ℕ} (hd : 2 ≤ d) {M a b : ℝ} (ha : 0 ≤ a) (haM : a ≤ M)
    (hb : 0 ≤ b) (hbM : b ≤ M) :
    |a ^ (d - 1) - b ^ (d - 1)| ≤ ((d : ℝ) - 1) * M ^ (d - 2) * |a - b| := by
  have h := abs_pow_sub_pow_le_box ha haM hb hbM (d - 1)
  have e1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  have e2 : d - 1 - 1 = d - 2 := by omega
  rwa [e1, e2] at h

/-- On the probability space `unitμ` the `L^{4/3}` functional is dominated by the `L⁴` one,
`‖g‖_{4/3} ≤ ‖g‖₄`.

Proved directly by Hölder with the conjugate pair `(3, 3/2)` applied to `|g|^{4/3} · 1`, which
gives `∫|g|^{4/3} ≤ (∫|g|⁴)^{1/3}`; raising to the power `3/4` is the claim.  (Mathlib's
`eLpNorm_le_eLpNorm_of_exponent_le` says the same thing for `eLpNorm`, but the translation to
raw integrals costs more than this proof.) -/
theorem Lnorm_43_le_Lnorm_4 (hg : Measurable g) (hgb : ∀ y, |g y| ≤ Cg) :
    Lnorm unitμ (4 / 3) g ≤ Lnorm unitμ 4 g := by
  have hmeas43 : Measurable fun y => |g y| ^ ((4 : ℝ) / 3) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4 / 3)).measurable.comp hg.abs
  have hpq : Real.HolderConjugate 3 (3 / 2) := ⟨by norm_num, by norm_num, by norm_num⟩
  have hf : MemLp (fun y => |g y| ^ ((4 : ℝ) / 3)) (ENNReal.ofReal 3) unitμ :=
    MemLp.of_bound hmeas43.aestronglyMeasurable (Cg ^ ((4 : ℝ) / 3))
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) (hgb y) (by norm_num))
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (3 / 2)) unitμ := memLp_const 1
  have hol := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg (g y)) _)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hf hone
  have e1 : ∫ a, (|g a| ^ ((4 : ℝ) / 3)) ^ (3 : ℝ) ∂unitμ = ∫ a, |g a| ^ (4 : ℝ) ∂unitμ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show (|g a| ^ ((4 : ℝ) / 3)) ^ (3 : ℝ) = |g a| ^ (4 : ℝ)
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hB : ∫ a, |g a| ^ ((4 : ℝ) / 3) ∂unitμ
      ≤ (∫ a, |g a| ^ (4 : ℝ) ∂unitμ) ^ (1 / (3 : ℝ)) := by
    calc ∫ a, |g a| ^ ((4 : ℝ) / 3) ∂unitμ = ∫ a, |g a| ^ ((4 : ℝ) / 3) * 1 ∂unitμ := by simp
      _ ≤ (∫ a, (|g a| ^ ((4 : ℝ) / 3)) ^ (3 : ℝ) ∂unitμ) ^ (1 / (3 : ℝ))
            * (∫ _a : ℝ, (1 : ℝ) ^ ((3 : ℝ) / 2) ∂unitμ) ^ (1 / ((3 : ℝ) / 2)) := hol
      _ = (∫ a, |g a| ^ (4 : ℝ) ∂unitμ) ^ (1 / (3 : ℝ)) := by rw [e1]; simp
  have h3 := Real.rpow_le_rpow (integral_abs_rpow_nonneg unitμ ((4 : ℝ) / 3) g) hB
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  rw [← Real.rpow_mul (integral_abs_rpow_nonneg unitμ (4 : ℝ) g),
    show 1 / (3 : ℝ) * (3 / 4) = 1 / 4 by norm_num] at h3
  unfold Lnorm
  rwa [show 1 / ((4 : ℝ) / 3) = 3 / 4 by norm_num]

/-- **Jensen for `t ↦ t^n`, via Bernoulli's inequality**: if `φ ≥ 0` has unit mass on the
probability space `unitμ`, then `∫ φ^n ≥ 1`.

The pointwise input is `1 + n(t-1) ≤ t^n` for `t ≥ 0` (`one_add_mul_le_pow`), whose integral is
exactly `1`.  No convexity API and no `⨍` averages are needed. -/
theorem one_le_integral_pow {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) (hi : Integrable φ unitμ)
    (h1 : ∫ x, φ x ∂unitμ = 1) (n : ℕ) (hp : Integrable (fun x => φ x ^ n) unitμ) :
    1 ≤ ∫ x, φ x ^ n ∂unitμ := by
  have key : ∀ x, 1 + (n : ℝ) * (φ x - 1) ≤ φ x ^ n := by
    intro x
    have hb : (-2 : ℝ) ≤ φ x - 1 := by linarith [hφ x]
    have hbern := one_add_mul_le_pow hb n
    rwa [show (1 : ℝ) + (φ x - 1) = φ x from by ring] at hbern
  have hsub : Integrable (fun x => φ x - 1) unitμ := hi.sub (integrable_const 1)
  have hlin : Integrable (fun x => 1 + (n : ℝ) * (φ x - 1)) unitμ :=
    (integrable_const 1).add (hsub.const_mul _)
  have hmono := integral_mono hlin hp key
  have hval : ∫ x, (1 + (n : ℝ) * (φ x - 1)) ∂unitμ = 1 := by
    rw [integral_add (integrable_const 1) (hsub.const_mul _), integral_const_mul,
      integral_sub hi (integrable_const 1)]
    simp [h1]
  rwa [hval] at hmono

/-- The `d`-flavoured form of `one_le_integral_pow`: `∫ φ^{d-1} ≥ 1` for a nonnegative `φ` of
unit mass.  This is what pins the normalisation of the Factor factor. -/
theorem one_le_integral_pow_sub_one {d : ℕ} {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x)
    (hi : Integrable φ unitμ) (h1 : ∫ x, φ x ∂unitμ = 1)
    (hp : Integrable (fun x => φ x ^ (d - 1)) unitμ) :
    1 ≤ ∫ x, φ x ^ (d - 1) ∂unitμ :=
  one_le_integral_pow hφ hi h1 (d - 1) hp

end SingularEndpoint

end UpperTailOptimizers
