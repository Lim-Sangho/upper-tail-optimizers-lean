import UpperTailOptimizers.SingularEndpoint.LocalizationRankOne.FactorHDensity

/-!
# Three-edge bounds for a general bounded symmetric kernel

The estimates `core_bound`, `peel_leaf`, `peel_double` and `walk3_bound` of
`SingularEndpoint/LocalizationRankOne/FactorHDensity.lean` use nothing about the rank-one decomposition except that
its residual is a bounded, measurable, symmetric kernel.  This file restates them for such a
kernel (`BKernel`), so that they apply to `W - ε` in the star reduction of the bipodality
proof.  The proofs are those of `SingularEndpoint/LocalizationRankOne/FactorHDensity.lean`, verbatim up to the
namespace.
-/

namespace UpperTailOptimizers

open MeasureTheory

/-- A bounded (by `5`), measurable, symmetric kernel on `ℝ²`. -/
structure BKernel where
  E : ℝ → ℝ → ℝ
  meas : Measurable (fun z : ℝ × ℝ => E z.1 z.2)
  bound : ∀ x y, |E x y| ≤ 5
  symm' : ∀ x y, E x y = E y x

namespace BKernel

variable (P : BKernel)

/-- The kernel itself, under the name used by the copied estimates. -/
def resid (x y : ℝ) : ℝ := P.E x y

theorem abs_resid_le (x y : ℝ) : |P.resid x y| ≤ 5 := P.bound x y

theorem measurable_resid : Measurable (fun z : ℝ × ℝ => P.resid z.1 z.2) := P.meas

theorem measurable_resid_right (x : ℝ) : Measurable (fun y => P.resid x y) :=
  P.meas.comp (measurable_const.prodMk measurable_id)

theorem resid_symm (x y : ℝ) : P.resid x y = P.resid y x := P.symm' x y

/-- `‖E‖₂²`. -/
noncomputable def residSq : ℝ := ∫ z, P.resid z.1 z.2 ^ 2 ∂gμ

theorem residSq_nonneg : 0 ≤ P.residSq := integral_nonneg fun _ => sq_nonneg _

theorem integrable_resid_sq : Integrable (fun z : ℝ × ℝ => P.resid z.1 z.2 ^ 2) gμ :=
  integrable_of_abs_le (P.measurable_resid.pow_const 2) 25 fun z => by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (P.resid z.1 z.2), P.abs_resid_le z.1 z.2, abs_nonneg (P.resid z.1 z.2)]

/-- The residual norm `‖E‖₂`.  The squared norm `residSq`, its nonnegativity and the
integrability of `E²` come from `SingularEndpoint/LocalizationRankOne/FactorStability.lean`, which owns that family. -/
noncomputable def residL2 : ℝ := Real.sqrt P.residSq


/-- `‖E‖₂ ≥ 0`. -/
theorem residL2_nonneg : 0 ≤ P.residL2 := Real.sqrt_nonneg _

/-- `‖E‖₂² is the square of ‖E‖₂`. -/
theorem residL2_sq : P.residL2 ^ 2 = P.residSq := Real.sq_sqrt P.residSq_nonneg

/-- The row norm `g(t) = (∫ E(t,s)² ds)^{1/2}` of the residual. -/
noncomputable def rowNorm (t : ℝ) : ℝ := Real.sqrt (∫ s, P.resid t s ^ 2 ∂unitμ)

/-- The row norm is nonnegative. -/
theorem rowNorm_nonneg (t : ℝ) : 0 ≤ P.rowNorm t := Real.sqrt_nonneg _

/-- The row norm is bounded by `5`, since `|E| ≤ 5`. -/
theorem rowNorm_le (t : ℝ) : P.rowNorm t ≤ 5 := by
  have hle : (∫ s, P.resid t s ^ 2 ∂unitμ) ≤ 25 := by
    have hint : Integrable (fun s => P.resid t s ^ 2) unitμ :=
      integrable_of_abs_le ((P.measurable_resid_right t).pow_const 2) 25 fun s => by
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_abs (P.resid t s), P.abs_resid_le t s, abs_nonneg (P.resid t s)]
    have := integral_mono hint (integrable_const (25:ℝ)) fun s => by
      nlinarith [sq_abs (P.resid t s), P.abs_resid_le t s, abs_nonneg (P.resid t s)]
    simpa using this
  calc P.rowNorm t ≤ Real.sqrt 25 := Real.sqrt_le_sqrt hle
    _ = 5 := by
        rw [show (25:ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]

/-- The row norm is measurable. -/
theorem measurable_rowNorm : Measurable P.rowNorm := by
  have h : Measurable fun t : ℝ => ∫ s, P.resid t s ^ 2 ∂unitμ :=
    ((P.measurable_resid.pow_const 2).stronglyMeasurable).integral_prod_right'.measurable
  exact Real.continuous_sqrt.measurable.comp h

/-- Fubini: `∫ g(t)² dt = ‖E‖₂²`. -/
theorem integral_rowNorm_sq : ∫ t, P.rowNorm t ^ 2 ∂unitμ = P.residSq := by
  have hpt : ∀ t : ℝ, P.rowNorm t ^ 2 = ∫ s, P.resid t s ^ 2 ∂unitμ := fun t =>
    Real.sq_sqrt (integral_nonneg fun s => sq_nonneg _)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  show ∫ t, ∫ s, P.resid t s ^ 2 ∂unitμ ∂unitμ = ∫ z, P.resid z.1 z.2 ^ 2 ∂gμ
  exact integral_integral P.integrable_resid_sq

/-- `∫ |E(t,s)| ds ≤ g(t)`, by Cauchy–Schwarz on the probability space. -/
theorem integral_abs_resid_le (t : ℝ) : ∫ s, |P.resid t s| ∂unitμ ≤ P.rowNorm t := by
  have h1 : Integrable (fun s => P.resid t s) unitμ :=
    integrable_of_abs_le (P.measurable_resid_right t) 5 fun s => P.abs_resid_le t s
  have h2 : Integrable (fun s => P.resid t s ^ 2) unitμ :=
    integrable_of_abs_le ((P.measurable_resid_right t).pow_const 2) 25 fun s => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (P.resid t s), P.abs_resid_le t s, abs_nonneg (P.resid t s)]
  exact integral_abs_le_sqrt h1 h2

/-- `∫ |E(t,s)| |E(t',s)| ds ≤ g(t) g(t')`, by Cauchy–Schwarz. -/
theorem integral_abs_resid_mul_le (t t' : ℝ) :
    ∫ s, |P.resid t s| * |P.resid t' s| ∂unitμ ≤ P.rowNorm t * P.rowNorm t' := by
  have hsq : ∀ r : ℝ, Integrable (fun s => |P.resid r s| ^ 2) unitμ := fun r =>
    integrable_of_abs_le (((P.measurable_resid_right r).abs).pow_const 2) 25 fun s => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (P.resid r s), P.abs_resid_le r s, abs_nonneg (P.resid r s)]
  have hmul : Integrable (fun s => |P.resid t s| * |P.resid t' s|) unitμ :=
    integrable_of_abs_le (((P.measurable_resid_right t).abs).mul
      ((P.measurable_resid_right t').abs)) 25 fun s => by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [P.abs_resid_le t s, P.abs_resid_le t' s, abs_nonneg (P.resid t s),
        abs_nonneg (P.resid t' s)]
  have h := integral_mul_le_sqrt_mul_sqrt (μ := unitμ) (f := fun s => |P.resid t s|)
    (g := fun s => |P.resid t' s|) (hsq t) (hsq t') hmul
  have e1 : ∫ s, |P.resid t s| ^ 2 ∂unitμ = ∫ s, P.resid t s ^ 2 ∂unitμ := by simp [sq_abs]
  have e2 : ∫ s, |P.resid t' s| ^ 2 ∂unitμ = ∫ s, P.resid t' s ^ 2 ∂unitμ := by simp [sq_abs]
  rw [e1, e2] at h
  exact h

/-! ## The three-edge bound -/

/-- `y ↦ E(y a, y b)` is measurable on the vertex product space. -/
theorem measurable_residAt {V : Type*} (a b : V) :
    Measurable fun y : V → ℝ => P.resid (y a) (y b) := by
  have hpair : Measurable fun y : V → ℝ => (y a, y b) := by fun_prop
  exact P.measurable_resid.comp hpair

/-- `y ↦ g(y a)` is measurable on the vertex product space. -/
theorem measurable_rowNormAt {V : Type*} (a : V) :
    Measurable fun y : V → ℝ => P.rowNorm (y a) :=
  P.measurable_rowNorm.comp (measurable_pi_apply a)

/-- **The core Cauchy–Schwarz bound**: for distinct vertices `a ≠ b`,
`∫ |E(y a, y b)| g(y a) g(y b) ≤ ‖E‖₂³`.

The pair marginal of the product measure at two distinct coordinates is `gμ`, and then
Cauchy–Schwarz against `‖E‖₂` leaves `(∫g²)^{1/2·2} = ‖E‖₂²`. -/
theorem core_bound {V : Type*} [Fintype V] [DecidableEq V] {a b : V} (hab : a ≠ b) :
    ∫ y : V → ℝ, |P.resid (y a) (y b)| * P.rowNorm (y a) * P.rowNorm (y b)
        ∂(Measure.pi fun _ : V => unitμ) ≤ P.residL2 ^ 3 := by
  have hmeasZ : Measurable fun z : ℝ × ℝ =>
      |P.resid z.1 z.2| * P.rowNorm z.1 * P.rowNorm z.2 :=
    ((P.measurable_resid.abs).mul (P.measurable_rowNorm.comp measurable_fst)).mul
      (P.measurable_rowNorm.comp measurable_snd)
  have htrans : ∫ y : V → ℝ, |P.resid (y a) (y b)| * P.rowNorm (y a) * P.rowNorm (y b)
        ∂(Measure.pi fun _ : V => unitμ)
      = ∫ z : ℝ × ℝ, |P.resid z.1 z.2| * P.rowNorm z.1 * P.rowNorm z.2 ∂gμ := by
    have hmp := measurePreserving_pair (V := V) hab
    show _ = ∫ z : ℝ × ℝ, |P.resid z.1 z.2| * P.rowNorm z.1 * P.rowNorm z.2
      ∂(unitμ.prod unitμ)
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hmeasZ.aestronglyMeasurable]
  rw [htrans]
  -- Cauchy–Schwarz with `f = |E|` and `g = g ⊗ g`
  have hf2 : Integrable (fun z : ℝ × ℝ => |P.resid z.1 z.2| ^ 2) gμ :=
    integrable_of_abs_le ((P.measurable_resid.abs).pow_const 2) 25 fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [P.abs_resid_le z.1 z.2, abs_nonneg (P.resid z.1 z.2)]
  have hrow : ∀ z : ℝ × ℝ, P.rowNorm z.1 * P.rowNorm z.2 ≤ 25 := fun z => by
    nlinarith [P.rowNorm_le z.1, P.rowNorm_le z.2, P.rowNorm_nonneg z.1,
      P.rowNorm_nonneg z.2]
  have hrow0 : ∀ z : ℝ × ℝ, (0:ℝ) ≤ P.rowNorm z.1 * P.rowNorm z.2 := fun z =>
    mul_nonneg (P.rowNorm_nonneg z.1) (P.rowNorm_nonneg z.2)
  have hg2 : Integrable (fun z : ℝ × ℝ => (P.rowNorm z.1 * P.rowNorm z.2) ^ 2) gμ :=
    integrable_of_abs_le (((P.measurable_rowNorm.comp measurable_fst).mul
      (P.measurable_rowNorm.comp measurable_snd)).pow_const 2) 625 fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hrow z, hrow0 z]
  have hfg : Integrable
      (fun z : ℝ × ℝ => |P.resid z.1 z.2| * (P.rowNorm z.1 * P.rowNorm z.2)) gμ :=
    integrable_of_abs_le ((P.measurable_resid.abs).mul
      ((P.measurable_rowNorm.comp measurable_fst).mul
        (P.measurable_rowNorm.comp measurable_snd))) 125 fun z => by
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (hrow0 z))]
      nlinarith [P.abs_resid_le z.1 z.2, abs_nonneg (P.resid z.1 z.2), hrow z, hrow0 z]
  have hcs := integral_mul_le_sqrt_mul_sqrt (μ := gμ) hf2 hg2 hfg
  have hre : ∫ z : ℝ × ℝ, |P.resid z.1 z.2| * P.rowNorm z.1 * P.rowNorm z.2 ∂gμ
      = ∫ z : ℝ × ℝ, |P.resid z.1 z.2| * (P.rowNorm z.1 * P.rowNorm z.2) ∂gμ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have e1 : ∫ z : ℝ × ℝ, |P.resid z.1 z.2| ^ 2 ∂gμ = P.residSq := by
    simp only [residSq, sq_abs]
  have e2 : ∫ z : ℝ × ℝ, (P.rowNorm z.1 * P.rowNorm z.2) ^ 2 ∂gμ = P.residSq ^ 2 := by
    have hpt : ∀ z : ℝ × ℝ, (P.rowNorm z.1 * P.rowNorm z.2) ^ 2
        = P.rowNorm z.1 ^ 2 * P.rowNorm z.2 ^ 2 := fun z => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      show gμ = unitμ.prod unitμ from rfl,
      integral_prod_mul (fun t : ℝ => P.rowNorm t ^ 2) (fun t : ℝ => P.rowNorm t ^ 2),
      P.integral_rowNorm_sq]
    ring
  rw [hre]
  refine le_trans hcs (le_of_eq ?_)
  rw [e1, e2, Real.sqrt_sq P.residSq_nonneg]
  show P.residL2 * P.residSq = P.residL2 ^ 3
  rw [← P.residL2_sq]; ring

/-- **Integrating out a leaf coordinate.**  If `K` does not depend on the coordinate `w`,
then `∫ K·|E(y a, y w)| ≤ ∫ K·g(y a)`. -/
theorem peel_leaf {V : Type*} [Fintype V] [DecidableEq V] {w a : V} (haw : a ≠ w)
    {K : (V → ℝ) → ℝ} {CK : ℝ} (hK : Measurable K) (hKb : ∀ y, |K y| ≤ CK)
    (hKnn : ∀ y, 0 ≤ K y) (hKupd : ∀ y s, K (Function.update y w s) = K y) :
    ∫ y : V → ℝ, K y * |P.resid (y a) (y w)| ∂(Measure.pi fun _ : V => unitμ)
      ≤ ∫ y : V → ℝ, K y * P.rowNorm (y a) ∂(Measure.pi fun _ : V => unitμ) := by
  refine integral_pi_le_of_update_le w (C := CK * 5) (D := CK * 5)
    (hK.mul ((P.measurable_residAt a w).abs))
    (hK.mul (P.measurable_rowNormAt a)) (fun y => ?_) (fun y => ?_) (fun y => ?_)
  · rw [abs_mul, abs_abs]
    exact mul_le_mul (hKb y) (P.abs_resid_le _ _) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hKb y))
  · rw [abs_mul, abs_of_nonneg (P.rowNorm_nonneg _)]
    exact mul_le_mul (hKb y) (P.rowNorm_le _) (P.rowNorm_nonneg _)
      (le_trans (abs_nonneg _) (hKb y))
  · have hupd : ∀ s : ℝ, K (Function.update y w s)
        * |P.resid (Function.update y w s a) (Function.update y w s w)|
        = K y * |P.resid (y a) s| := by
      intro s
      rw [hKupd, Function.update_of_ne haw, Function.update_self]
    calc ∫ s, K (Function.update y w s)
          * |P.resid (Function.update y w s a) (Function.update y w s w)| ∂unitμ
        = ∫ s, K y * |P.resid (y a) s| ∂unitμ :=
          integral_congr_ae (Filter.Eventually.of_forall hupd)
      _ = K y * ∫ s, |P.resid (y a) s| ∂unitμ := integral_const_mul _ _
      _ ≤ K y * P.rowNorm (y a) :=
          mul_le_mul_of_nonneg_left (P.integral_abs_resid_le (y a)) (hKnn y)

/-- **Integrating out a coordinate shared by two residual edges.**  If `K` does not depend
on `w`, then `∫ K·|E(y a, y w)|·|E(y b, y w)| ≤ ∫ K·g(y a)·g(y b)`. -/
theorem peel_double {V : Type*} [Fintype V] [DecidableEq V] {w a b : V} (haw : a ≠ w)
    (hbw : b ≠ w) {K : (V → ℝ) → ℝ} {CK : ℝ} (hK : Measurable K) (hKb : ∀ y, |K y| ≤ CK)
    (hKnn : ∀ y, 0 ≤ K y) (hKupd : ∀ y s, K (Function.update y w s) = K y) :
    ∫ y : V → ℝ, K y * (|P.resid (y a) (y w)| * |P.resid (y b) (y w)|)
        ∂(Measure.pi fun _ : V => unitμ)
      ≤ ∫ y : V → ℝ, K y * (P.rowNorm (y a) * P.rowNorm (y b))
        ∂(Measure.pi fun _ : V => unitμ) := by
  refine integral_pi_le_of_update_le w (C := CK * 25) (D := CK * 25)
    (hK.mul (((P.measurable_residAt a w).abs).mul ((P.measurable_residAt b w).abs)))
    (hK.mul ((P.measurable_rowNormAt a).mul (P.measurable_rowNormAt b)))
    (fun y => ?_) (fun y => ?_) (fun y => ?_)
  · have h2 : (0:ℝ) ≤ |P.resid (y a) (y w)| * |P.resid (y b) (y w)| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h1 : |P.resid (y a) (y w)| * |P.resid (y b) (y w)| ≤ 25 := by
      nlinarith [P.abs_resid_le (y a) (y w), P.abs_resid_le (y b) (y w),
        abs_nonneg (P.resid (y a) (y w)), abs_nonneg (P.resid (y b) (y w))]
    calc |K y * (|P.resid (y a) (y w)| * |P.resid (y b) (y w)|)|
        = |K y| * (|P.resid (y a) (y w)| * |P.resid (y b) (y w)|) := by
          rw [abs_mul, abs_of_nonneg h2]
      _ ≤ CK * 25 := mul_le_mul (hKb y) h1 h2 (le_trans (abs_nonneg _) (hKb y))
  · have h2 : (0:ℝ) ≤ P.rowNorm (y a) * P.rowNorm (y b) :=
      mul_nonneg (P.rowNorm_nonneg _) (P.rowNorm_nonneg _)
    have h1 : P.rowNorm (y a) * P.rowNorm (y b) ≤ 25 := by
      nlinarith [P.rowNorm_le (y a), P.rowNorm_le (y b), P.rowNorm_nonneg (y a),
        P.rowNorm_nonneg (y b)]
    calc |K y * (P.rowNorm (y a) * P.rowNorm (y b))|
        = |K y| * (P.rowNorm (y a) * P.rowNorm (y b)) := by
          rw [abs_mul, abs_of_nonneg h2]
      _ ≤ CK * 25 := mul_le_mul (hKb y) h1 h2 (le_trans (abs_nonneg _) (hKb y))
  · have hupd : ∀ s : ℝ, K (Function.update y w s)
        * (|P.resid (Function.update y w s a) (Function.update y w s w)|
          * |P.resid (Function.update y w s b) (Function.update y w s w)|)
        = K y * (|P.resid (y a) s| * |P.resid (y b) s|) := by
      intro s
      rw [hKupd, Function.update_of_ne haw, Function.update_of_ne hbw, Function.update_self]
    calc ∫ s, K (Function.update y w s)
          * (|P.resid (Function.update y w s a) (Function.update y w s w)|
            * |P.resid (Function.update y w s b) (Function.update y w s w)|) ∂unitμ
        = ∫ s, K y * (|P.resid (y a) s| * |P.resid (y b) s|) ∂unitμ :=
          integral_congr_ae (Filter.Eventually.of_forall hupd)
      _ = K y * ∫ s, |P.resid (y a) s| * |P.resid (y b) s| ∂unitμ := integral_const_mul _ _
      _ ≤ K y * (P.rowNorm (y a) * P.rowNorm (y b)) :=
          mul_le_mul_of_nonneg_left (P.integral_abs_resid_mul_le (y a) (y b)) (hKnn y)

/-- **The three-edge walk bound.**  For a walk `s(a,b), s(a,c), s(b,v)` (with `c = v`
allowed, i.e. a triangle),

`∫ |E(y a, y b)| |E(y a, y c)| |E(y b, y v)| ≤ ‖E‖₂³`.

In the triangle case the shared coordinate `c = v` is integrated out by `peel_double`; in
the path case the two ends `c` and `v` are integrated out one at a time by `peel_leaf`.
Either way one lands on `core_bound`. -/
theorem walk3_bound {V : Type*} [Fintype V] [DecidableEq V] {a b c v : V} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hva : v ≠ a) (hvb : v ≠ b) :
    ∫ y : V → ℝ, |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)|
        ∂(Measure.pi fun _ : V => unitμ) ≤ P.residL2 ^ 3 := by
  by_cases hcv : c = v
  · subst hcv
    -- the triangle case: peel the shared coordinate `c`
    have hK : Measurable fun y : V → ℝ => |P.resid (y a) (y b)| :=
      (P.measurable_residAt a b).abs
    have hKb : ∀ y : V → ℝ, |(|P.resid (y a) (y b)|)| ≤ 5 := fun y => by
      rw [abs_abs]; exact P.abs_resid_le _ _
    have hKnn : ∀ y : V → ℝ, 0 ≤ |P.resid (y a) (y b)| := fun y => abs_nonneg _
    have hKupd : ∀ (y : V → ℝ) (s : ℝ),
        |P.resid (Function.update y c s a) (Function.update y c s b)|
          = |P.resid (y a) (y b)| := fun y s => by
      rw [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hcb)]
    have hstep := P.peel_double (w := c) (a := a) (b := b) (Ne.symm hca) (Ne.symm hcb)
      hK hKb hKnn hKupd
    have hre1 : ∫ y : V → ℝ,
          |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y c)|
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ,
          |P.resid (y a) (y b)| * (|P.resid (y a) (y c)| * |P.resid (y b) (y c)|)
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have hre2 : ∫ y : V → ℝ,
          |P.resid (y a) (y b)| * (P.rowNorm (y a) * P.rowNorm (y b))
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ, |P.resid (y a) (y b)| * P.rowNorm (y a) * P.rowNorm (y b)
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [hre1]
    exact le_trans (le_trans hstep (le_of_eq hre2)) (P.core_bound hab)
  · -- the path case: peel `c`, then `v`
    have hvc : v ≠ c := fun h => hcv h.symm
    have hK1 : Measurable fun y : V → ℝ =>
        |P.resid (y a) (y b)| * |P.resid (y b) (y v)| :=
      ((P.measurable_residAt a b).abs).mul ((P.measurable_residAt b v).abs)
    have hK1b : ∀ y : V → ℝ,
        |(|P.resid (y a) (y b)| * |P.resid (y b) (y v)|)| ≤ 25 := fun y => by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [P.abs_resid_le (y a) (y b), P.abs_resid_le (y b) (y v),
        abs_nonneg (P.resid (y a) (y b)), abs_nonneg (P.resid (y b) (y v))]
    have hK1nn : ∀ y : V → ℝ, 0 ≤ |P.resid (y a) (y b)| * |P.resid (y b) (y v)| :=
      fun y => by positivity
    have hK1upd : ∀ (y : V → ℝ) (s : ℝ),
        |P.resid (Function.update y c s a) (Function.update y c s b)|
          * |P.resid (Function.update y c s b) (Function.update y c s v)|
        = |P.resid (y a) (y b)| * |P.resid (y b) (y v)| := fun y s => by
      rw [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hcb),
        Function.update_of_ne hvc]
    have hstep1 := P.peel_leaf (w := c) (a := a) (Ne.symm hca) hK1 hK1b hK1nn hK1upd
    have hK2 : Measurable fun y : V → ℝ => |P.resid (y a) (y b)| * P.rowNorm (y a) :=
      ((P.measurable_residAt a b).abs).mul (P.measurable_rowNormAt a)
    have hK2nn : ∀ y : V → ℝ, 0 ≤ |P.resid (y a) (y b)| * P.rowNorm (y a) := fun y =>
      mul_nonneg (abs_nonneg _) (P.rowNorm_nonneg _)
    have hK2b : ∀ y : V → ℝ, |(|P.resid (y a) (y b)| * P.rowNorm (y a))| ≤ 25 := fun y => by
      rw [abs_of_nonneg (hK2nn y)]
      nlinarith [P.abs_resid_le (y a) (y b), abs_nonneg (P.resid (y a) (y b)),
        P.rowNorm_le (y a), P.rowNorm_nonneg (y a)]
    have hK2upd : ∀ (y : V → ℝ) (s : ℝ),
        |P.resid (Function.update y v s a) (Function.update y v s b)|
          * P.rowNorm (Function.update y v s a)
        = |P.resid (y a) (y b)| * P.rowNorm (y a) := fun y s => by
      rw [Function.update_of_ne (Ne.symm hva), Function.update_of_ne (Ne.symm hvb)]
    have hstep2 := P.peel_leaf (w := v) (a := b) (Ne.symm hvb) hK2 hK2b hK2nn hK2upd
    have hre1 : ∫ y : V → ℝ,
          |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)|
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ,
          (|P.resid (y a) (y b)| * |P.resid (y b) (y v)|) * |P.resid (y a) (y c)|
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have hre2 : ∫ y : V → ℝ,
          (|P.resid (y a) (y b)| * |P.resid (y b) (y v)|) * P.rowNorm (y a)
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ,
          (|P.resid (y a) (y b)| * P.rowNorm (y a)) * |P.resid (y b) (y v)|
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have hre3 : ∫ y : V → ℝ,
          (|P.resid (y a) (y b)| * P.rowNorm (y a)) * P.rowNorm (y b)
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ, |P.resid (y a) (y b)| * P.rowNorm (y a) * P.rowNorm (y b)
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [hre1]
    refine le_trans hstep1 (le_trans (le_of_eq hre2) (le_trans hstep2 ?_))
    exact le_trans (le_of_eq hre3) (P.core_bound hab)


end BKernel

end UpperTailOptimizers
