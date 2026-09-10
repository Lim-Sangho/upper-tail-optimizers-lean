import UpperTailOptimizers.SingularEndpoint.Defs
import UpperTailOptimizers.SingularEndpoint.KernelOp

/-!
# The normalised contraction map of the nonlinear Factor construction (Section 7)

`lem:localization-rank-one` of `paper/singular_endpoint.tex` asserts, for a graphon `W` with
`‖W - r_*‖₄` small, existence and uniqueness of a nonnegative factor `f` solving the nonlinear
Factor equation `T_W(f^{d-1}) = q f` of `eq:rank-one-orthogonality`, together with the
closeness bound `eq:rank-one-reduction-bounds`.

The paper builds `f` variationally, maximising `Q_W` over the unit ball of `L^{d/(d-1)}`.  That
route needs weak compactness of the ball, hence reflexivity of `L^p` and the duality
`(L^p)^* = L^q`, neither of which this Mathlib has.  This file prepares the alternative route,
a **normalised contraction iteration** in `L⁴` for

`N(φ) := T_W(φ^{d-1}) / ∫ T_W(φ^{d-1})`

on the set `S = {φ : 0 ≤ φ ≤ M, ∫ φ = 1}` with `M = 2/r_*` (`ContractionMem`).  The point of
*normalising* is that the naive iteration `φ ↦ T_W(φ^{d-1})/∫φ^d` has derivative
`v ↦ -(∫v)·1` at the base point, of operator norm exactly `1`, whereas `N` is **identically
`1`** when `W ≡ r_*`, because the constant kernel has rank one.  Its whole first-order response
is therefore carried by `U := W - r_*`, and it contracts with factor `O(‖U‖₄)`.

## What is proved here

With `ε := ‖W - r_*‖_{L⁴([0,1]²)}` (`contractionEps`) and `ε ≤ ε₀(d)` (`contractionEps0`):

* `contractionMap_mem` — **self-map**: `φ ∈ S → N(φ) ∈ S`;
* `contractionMap_closeness` — **closeness**, free and linear in `ε`:
  `‖N(φ) - 1‖₄ ≤ 2M^d·ε` for *every* `φ ∈ S`, no small ball needed.  This is the raw-function
  precursor of the `‖f - u_*‖₄ ≤ Cε` half of `eq:rank-one-reduction-bounds`;
* `contractionMap_contraction` — **contraction**:
  `‖N(φ) - N(ψ)‖₄ ≤ C_contr(d)·ε·‖φ - ψ‖₄`, through the exact identity
  `contractionMap_sub_identity`.

All constants are explicit, depend only on `d`, and are fixed before `ε₀`.

## What is *not* proved here

No fixed point.  The Banach argument, the passage to `Lp` (needed because `S` is closed only up
to a.e. equality) and the normalisation `q = ∫ f^d` are `SingularEndpoint/FactorFix.lean`; the
orthogonality half of `eq:rank-one-orthogonality` and the closeness bounds of
`eq:rank-one-reduction-bounds`
are `SingularEndpoint/FactorSolution.lean`; the combined stability inequality is
`SingularEndpoint/FactorStability.lean`; and the assembly with the uniqueness clause is
`SingularEndpoint/FactorMain.lean` (`exists_factorDecomp`, `localization_rankOne`, `factorMain_unique`).
Nothing here mentions `FactorDecomp`.

## The contraction identity

The identity proposed for this construction,

`N(φ) - N(ψ) = (c(1 - N(ψ)) + e - N(ψ)∫e) / ∫A(φ)`,  `c = r_*∫(φ^{d-1} - ψ^{d-1})`,
`e = T_U(φ^{d-1} - ψ^{d-1})`,

is **correct**; `contractionMap_sub_identity` is exactly it.  (Proof: `A(φ) = A(ψ) + c + e`
pointwise and `D(φ) = D(ψ) + c + ∫e`, after which `contraction_quotient_identity` is pure algebra.)
Two features worth recording: the denominator is `∫A(φ)`, not `∫A(ψ)`; and the first numerator
term is small because `1 - N(ψ)` is small, *not* because `c` is — `c` is only
`O(‖φ - ψ‖₄)`, with no gain of `ε`.

## Design

Raw functions and `MeasureTheory.integral` throughout, as in `SingularEndpoint/KernelOp.lean`; the
`L^p` quantity is that file's `Lnorm`.  Minkowski for `Lnorm` at the single exponent `4` is
obtained by passing through `MeasureTheory.eLpNorm` (`contractionLnorm_add_le`); everything else is
proved directly from the definition.  The denominator of `N` is **floored** at `r_*/2`
(`contractionDen`) so that `contractionMap` is total and junk-free; `contractionDen_eq` shows the floor is
inactive on `S` under the standing smallness hypothesis, so that `contractionMap` agrees there with
the honest normalised map.

One naming caution: `ContractionMem.one_le_integral_pow` below is a two-line `ContractionMem` wrapper of
`SingularEndpoint.one_le_integral_pow_sub_one`, the `n = d-1` form of `SingularEndpoint.one_le_integral_pow`
(`SingularEndpoint/KernelOp.lean`) — not a second proof of the same Jensen bound.  Inside
`namespace ContractionMem` the bare name resolves to the wrapper.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

/-! ## Raw-function `L^p` tools

Four estimates for `Lnorm` that `SingularEndpoint/KernelOp.lean` does not provide: a uniform bound, a
scalar-majorant bound, Minkowski at `p = 4`, and `L¹ ≤ L⁴`.
-/

/-- The triangle inequality in the difference form used repeatedly below. -/
private theorem contraction_abs_sub_le {a b : ℝ} : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rwa [← sub_eq_add_neg, abs_neg] at h

/-- `‖h‖_{L^p(μ)} ≤ C` for a uniformly bounded `h` on a probability space. -/
theorem contractionLnorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 0 < p) {h : α → ℝ} {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |h x| ≤ C) :
    Lnorm μ p h ≤ C := by
  have hle : ∫ x, |h x| ^ p ∂μ ≤ C ^ p := by
    have h1 := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (h x)) p)
      (integrable_const (μ := μ) (C ^ p))
      (Filter.Eventually.of_forall fun x => Real.rpow_le_rpow (abs_nonneg _) (hb x) hp.le)
    simpa using h1
  have h2 := Real.rpow_le_rpow (integral_abs_rpow_nonneg μ p h) hle (one_div_nonneg.mpr hp.le)
  unfold Lnorm
  rwa [← Real.rpow_mul hC, mul_one_div, div_self hp.ne', Real.rpow_one] at h2

/-- If `|f| ≤ c|g|` pointwise with `c ≥ 0` and `g` bounded measurable, then
`‖f‖_{L^p(μ)} ≤ c‖g‖_{L^p(μ)}`.  Both the scaling and the monotonicity of `Lnorm` are used only
through this one statement; `f` itself need not be measurable. -/
theorem contractionLnorm_le_const_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {p : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) {f g : α → ℝ}
    (hg : Measurable g) {Cg : ℝ} (hgb : ∀ x, |g x| ≤ Cg) (hfg : ∀ x, |f x| ≤ c * |g x|) :
    Lnorm μ p f ≤ c * Lnorm μ p g := by
  have hmg : Measurable fun x => |g x| ^ p :=
    (Real.continuous_rpow_const hp.le).measurable.comp hg.abs
  have hint : Integrable (fun x => c ^ p * |g x| ^ p) μ := by
    refine integrable_of_abs_le (measurable_const.mul hmg) (c ^ p * Cg ^ p) fun x => ?_
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hc _) (Real.rpow_nonneg (abs_nonneg _) _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (hgb x) hp.le)
      (Real.rpow_nonneg hc _)
  have hstep : ∫ x, |f x| ^ p ∂μ ≤ c ^ p * ∫ x, |g x| ^ p ∂μ := by
    have h1 := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (f x)) p) hint
      (Filter.Eventually.of_forall fun x => by
        have h2 := Real.rpow_le_rpow (abs_nonneg (f x)) (hfg x) hp.le
        rwa [Real.mul_rpow hc (abs_nonneg _)] at h2)
    rwa [integral_const_mul] at h1
  have h3 := Real.rpow_le_rpow (integral_abs_rpow_nonneg μ p f) hstep (one_div_nonneg.mpr hp.le)
  unfold Lnorm
  rwa [Real.mul_rpow (Real.rpow_nonneg hc _) (integral_abs_rpow_nonneg μ p g),
    ← Real.rpow_mul hc, mul_one_div, div_self hp.ne', Real.rpow_one] at h3

/-- **Minkowski for `Lnorm` at `p = 4`**, for bounded measurable functions on `unitμ`.

`Lnorm` is a raw integral expression, not a Mathlib `Lp` norm, so subadditivity is not free.
The proof identifies `Lnorm unitμ 4 h` with `eLpNorm h 4 unitμ` through
`MemLp.eLpNorm_eq_integral_rpow_norm` and quotes `eLpNorm_add_le`. -/
theorem contractionLnorm_add_le {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) {Cf Cg : ℝ}
    (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg) :
    Lnorm unitμ 4 (fun x => f x + g x) ≤ Lnorm unitμ 4 f + Lnorm unitμ 4 g := by
  have hmem : ∀ {h : ℝ → ℝ} {C : ℝ}, Measurable h → (∀ x, |h x| ≤ C) → MemLp h 4 unitμ := by
    intro h C hh hb
    exact MemLp.of_bound hh.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)
  have key : ∀ {h : ℝ → ℝ}, MemLp h 4 unitμ →
      eLpNorm h 4 unitμ = ENNReal.ofReal (Lnorm unitμ 4 h) := by
    intro h hh
    rw [hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp [Lnorm, Real.norm_eq_abs, one_div]
  have hmf := hmem hf hfb
  have hmg := hmem hg hgb
  have hsum : eLpNorm (f + g) 4 unitμ ≤ eLpNorm f 4 unitμ + eLpNorm g 4 unitμ :=
    eLpNorm_add_le (μ := unitμ) hf.aestronglyMeasurable hg.aestronglyMeasurable
      (by norm_num : (1 : ENNReal) ≤ 4)
  rw [key (hmf.add hmg), key hmf, key hmg,
    ← ENNReal.ofReal_add (Lnorm_nonneg _ _ _) (Lnorm_nonneg _ _ _)] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (Lnorm_nonneg _ _ _) (Lnorm_nonneg _ _ _))).mp hsum

/-- `∫ |h| ≤ ‖h‖₄` on the probability space `unitμ`: Hölder against the constant `1`.  This is
how a *mass* defect (an integral) is turned into an `L⁴` quantity. -/
theorem contractionIntegral_abs_le_Lnorm_four {h : ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) : ∫ x, |h x| ∂unitμ ≤ Lnorm unitμ 4 h := by
  have hpq : Real.HolderConjugate 4 (4 / 3) := ⟨by norm_num, by norm_num, by norm_num⟩
  have hf : MemLp (fun y => |h y|) (ENNReal.ofReal 4) unitμ :=
    MemLp.of_bound hm.abs.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa using hb y)
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (4 / 3)) unitμ := memLp_const 1
  have hol := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun y => abs_nonneg (h y))
    (Filter.Eventually.of_forall fun _ => zero_le_one) hf hone
  calc ∫ x, |h x| ∂unitμ = ∫ x, |h x| * 1 ∂unitμ := by simp
    _ ≤ (∫ a, |h a| ^ (4 : ℝ) ∂unitμ) ^ (1 / (4 : ℝ))
          * (∫ _a : ℝ, (1 : ℝ) ^ ((4 : ℝ) / 3) ∂unitμ) ^ (1 / ((4 : ℝ) / 3)) := hol
    _ = Lnorm unitμ 4 h := by simp [Lnorm]

/-! ## Pure algebra

Two scalar identities, isolated so that the analytic proofs below carry no division
bookkeeping.
-/

/-- `(r + e)/D - 1 = (e - i)/D` when `D = r + i`: the constant part `r` cancels. -/
private theorem contraction_div_sub_one {r ex ie D : ℝ} (hD : D ≠ 0) (hDe : D = r + ie) :
    (r + ex) / D - 1 = (ex - ie) / D := by
  have h : r + ex - D = ex - ie := by rw [hDe]; ring
  rw [← h, sub_div, div_self hD]

/-- **The contraction identity, in scalar form.**  If `a₁ = a₂ + c + e` and `D₁ = D₂ + c + i`
then `a₁/D₁ - a₂/D₂ = (c(1 - a₂/D₂) + e - (a₂/D₂)i)/D₁`. -/
private theorem contraction_quotient_identity {a₁ a₂ c e ie D₁ D₂ : ℝ} (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hD : D₁ = D₂ + c + ie) (ha : a₁ = a₂ + c + e) :
    a₁ / D₁ - a₂ / D₂ = (c * (1 - a₂ / D₂) + e - a₂ / D₂ * ie) / D₁ := by
  have ht : a₂ / D₂ * D₂ = a₂ := div_mul_cancel₀ a₂ hD₂
  rw [eq_div_iff hD₁, sub_mul, div_mul_cancel₀ a₁ hD₁, ha, hD]
  linear_combination -ht

/-! ## The constants -/

variable {d : ℕ} {W : Graphon} {φ ψ : ℝ → ℝ}

/-- The uniform bound `M = 2/r_*` defining the invariant set.  Since `r_* = (d-1)/d ∈ [1/2,1)`
for `d ≥ 2`, one has `2 < M ≤ 4`; only `M > 0` is used. -/
noncomputable def contractionM (d : ℕ) : ℝ := 2 / rStar d

/-- `M > 0`. -/
theorem contractionM_pos (hd : 2 ≤ d) : 0 < contractionM d :=
  div_pos (by norm_num) (rStar_pos hd)

/-- `M·r_* = 2`, the only arithmetic fact about `M` that is used. -/
theorem contractionM_mul_rStar (hd : 2 ≤ d) : contractionM d * rStar d = 2 :=
  div_mul_cancel₀ 2 (rStar_ne_zero hd)

/-- `M·M^{d-1} = M^d`, valid because `d ≥ 2` makes the truncated subtraction honest. -/
theorem contractionM_mul_pow (hd : 2 ≤ d) : contractionM d * contractionM d ^ (d - 1) = contractionM d ^ d := by
  have h1 : contractionM d ^ (d - 1) * contractionM d = contractionM d ^ (d - 1 + 1) := (pow_succ _ _).symm
  have h2 : d - 1 + 1 = d := by omega
  rw [h2] at h1
  rw [mul_comm]
  exact h1

/-- The power-Lipschitz constant `L_d = (d-1)M^{d-2}` of `t ↦ t^{d-1}` on `[0,M]`
(`abs_pow_sub_pow_le_deg`). -/
noncomputable def contractionLip (d : ℕ) : ℝ := ((d : ℝ) - 1) * contractionM d ^ (d - 2)

/-- `L_d ≥ 0`. -/
theorem contractionLip_nonneg (hd : 2 ≤ d) : 0 ≤ contractionLip d := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  exact mul_nonneg (by linarith) (pow_nonneg (contractionM_pos hd).le _)

/-- The residual kernel `U = W - r_*` of the rank-one reduction lemma. -/
noncomputable def contractionU (W : Graphon) (d : ℕ) : ℝ → ℝ → ℝ := fun x y => W.toFun x y - rStar d

/-- `U` is measurable as a function on the square. -/
theorem contraction_measurable_U (W : Graphon) (d : ℕ) :
    Measurable (Function.uncurry (contractionU W d)) := by
  show Measurable fun z : ℝ × ℝ => W.toFun z.1 z.2 - rStar d
  exact W.meas'.sub measurable_const

/-- `|U| ≤ 1`, since `W` and `r_*` both lie in `[0,1]`. -/
theorem contraction_abs_U_le (hd : 2 ≤ d) (W : Graphon) : ∀ x y, |contractionU W d x y| ≤ 1 := by
  intro x y
  have h0 := W.nonneg' x y
  have h1 := W.le_one' x y
  have hr0 := (rStar_pos hd).le
  have hr1 := (rStar_lt_one hd).le
  have hU : contractionU W d x y = W.toFun x y - rStar d := rfl
  rw [hU, abs_le]
  constructor <;> linarith

/-- The smallness parameter `ε = ‖W - r_*‖_{L⁴([0,1]²)}` of
`lem:localization-rank-one`. -/
noncomputable def contractionEps (W : Graphon) (d : ℕ) : ℝ :=
  Lnorm gμ 4 (fun z : ℝ × ℝ => contractionU W d z.1 z.2)

/-- `ε ≥ 0`. -/
theorem contractionEps_nonneg (W : Graphon) (d : ℕ) : 0 ≤ contractionEps W d := Lnorm_nonneg _ _ _

/-- The threshold `ε₀(d) = r_*/(2M^{d-1})`.  It depends only on `d`, and every constant in this
file is fixed before it. -/
noncomputable def contractionEps0 (d : ℕ) : ℝ := rStar d / (2 * contractionM d ^ (d - 1))

/-- `ε₀(d) > 0`. -/
theorem contractionEps0_pos (hd : 2 ≤ d) : 0 < contractionEps0 d :=
  div_pos (rStar_pos hd) (mul_pos (by norm_num) (pow_pos (contractionM_pos hd) _))

/-- The form in which the smallness hypothesis is consumed: `εM^{d-1} ≤ r_*/2`. -/
theorem contraction_eps_mul_le (hd : 2 ≤ d) (hε : contractionEps W d ≤ contractionEps0 d) :
    contractionEps W d * contractionM d ^ (d - 1) ≤ rStar d / 2 := by
  have hMp : (0 : ℝ) < contractionM d ^ (d - 1) := pow_pos (contractionM_pos hd) _
  calc contractionEps W d * contractionM d ^ (d - 1) ≤ contractionEps0 d * contractionM d ^ (d - 1) :=
        mul_le_mul_of_nonneg_right hε hMp.le
    _ = rStar d / 2 := by
        show rStar d / (2 * contractionM d ^ (d - 1)) * contractionM d ^ (d - 1) = rStar d / 2
        rw [div_mul_eq_mul_div, mul_comm (2 : ℝ) (contractionM d ^ (d - 1)), ← div_div,
          mul_div_assoc, div_self hMp.ne', mul_one]

/-- The closeness constant `C_close(d) = 2M^d`.  Equivalently `4M^{d-1}/r_*`; the present form
avoids all division. -/
noncomputable def contractionCloseConst (d : ℕ) : ℝ := 2 * contractionM d ^ d

/-- `C_close(d) > 0`. -/
theorem contractionCloseConst_pos (hd : 2 ≤ d) : 0 < contractionCloseConst d :=
  mul_pos (by norm_num) (pow_pos (contractionM_pos hd) _)

/-- `r_*·C_close(d) = 4M^{d-1}`: the cancellation that makes the first numerator term of the
contraction identity independent of `r_*`. -/
theorem rStar_mul_contractionCloseConst (hd : 2 ≤ d) :
    rStar d * contractionCloseConst d = 4 * contractionM d ^ (d - 1) := by
  simp only [contractionCloseConst]
  rw [← contractionM_mul_pow hd]
  linear_combination (2 * contractionM d ^ (d - 1)) * contractionM_mul_rStar hd

/-- The contraction constant `C_contr(d) = M(4M^{d-1} + 1 + M)L_d`. -/
noncomputable def contractionContrConst (d : ℕ) : ℝ :=
  contractionM d * (4 * contractionM d ^ (d - 1) + 1 + contractionM d) * contractionLip d

/-- `C_contr(d) ≥ 0`. -/
theorem contractionContrConst_nonneg (hd : 2 ≤ d) : 0 ≤ contractionContrConst d := by
  have hM := contractionM_pos hd
  have hk := pow_nonneg hM.le (d - 1)
  exact mul_nonneg (mul_nonneg hM.le (by linarith)) (contractionLip_nonneg hd)

/-! ## The invariant set `S` -/

/-- Membership in the invariant set `S = {φ : φ measurable, 0 ≤ φ ≤ M, ∫ φ = 1}` of the
normalised contraction iteration. -/
structure ContractionMem (d : ℕ) (φ : ℝ → ℝ) : Prop where
  /-- `φ` is measurable. -/
  meas : Measurable φ
  /-- `φ` is nonnegative. -/
  nonneg : ∀ x, 0 ≤ φ x
  /-- `φ` is bounded by `M = 2/r_*`. -/
  le_bound : ∀ x, φ x ≤ contractionM d
  /-- `φ` has unit mass. -/
  mass : ∫ x, φ x ∂unitμ = 1

namespace ContractionMem

/-- The two-sided bound `|φ| ≤ M`. -/
theorem abs_le (hd : 2 ≤ d) (hφ : ContractionMem d φ) (x : ℝ) : |φ x| ≤ contractionM d :=
  _root_.abs_le.mpr
    ⟨by have h1 := hφ.nonneg x; have h2 := (contractionM_pos hd).le; linarith, hφ.le_bound x⟩

/-- `φ^{d-1}` is measurable. -/
theorem measurable_pow (hφ : ContractionMem d φ) : Measurable fun y => φ y ^ (d - 1) :=
  hφ.meas.pow_const _

/-- `|φ^{d-1}| ≤ M^{d-1}`. -/
theorem abs_pow_le (hd : 2 ≤ d) (hφ : ContractionMem d φ) (y : ℝ) :
    |φ y ^ (d - 1)| ≤ contractionM d ^ (d - 1) := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hφ.abs_le hd y) _

/-- `φ` is integrable. -/
theorem integrable (hd : 2 ≤ d) (hφ : ContractionMem d φ) : Integrable φ unitμ :=
  integrable_of_abs_le hφ.meas _ (hφ.abs_le hd)

/-- `φ^{d-1}` is integrable. -/
theorem integrable_pow (hd : 2 ≤ d) (hφ : ContractionMem d φ) :
    Integrable (fun y => φ y ^ (d - 1)) unitμ :=
  integrable_of_abs_le hφ.measurable_pow _ (hφ.abs_pow_le hd)

/-- **Jensen**: `∫ φ^{d-1} ≥ 1` for a nonnegative `φ` of unit mass
(`one_le_integral_pow_sub_one`). -/
theorem one_le_integral_pow (hd : 2 ≤ d) (hφ : ContractionMem d φ) :
    1 ≤ ∫ y, φ y ^ (d - 1) ∂unitμ :=
  one_le_integral_pow_sub_one hφ.nonneg (hφ.integrable hd) hφ.mass (hφ.integrable_pow hd)

/-- `‖φ^{d-1}‖₄ ≤ M^{d-1}`. -/
theorem Lnorm_pow_le (hd : 2 ≤ d) (hφ : ContractionMem d φ) :
    Lnorm unitμ 4 (fun y => φ y ^ (d - 1)) ≤ contractionM d ^ (d - 1) :=
  contractionLnorm_le (by norm_num) (pow_nonneg (contractionM_pos hd).le _) (hφ.abs_pow_le hd)

end ContractionMem

/-! ## The map -/

/-- The numerator `A(φ) = T_W(φ^{d-1})` of the normalised contraction map. -/
noncomputable def contractionNum (W : Graphon) (d : ℕ) (φ : ℝ → ℝ) : ℝ → ℝ :=
  kernelOp W.toFun (fun y => φ y ^ (d - 1))

/-- The `U`-part of the numerator, `T_U(φ^{d-1})` with `U = W - r_*`.  The rank-one constant
part of `T_W` contributes only the constant `r_*∫φ^{d-1}` (`contractionNum_split`), so `contractionErr`
carries the entire non-constant response. -/
noncomputable def contractionErr (W : Graphon) (d : ℕ) (φ : ℝ → ℝ) : ℝ → ℝ :=
  kernelOp (contractionU W d) (fun y => φ y ^ (d - 1))

/-- The denominator `∫A(φ)`, **floored at `r_*/2`** so that `contractionMap` is total and junk-free.
On the invariant set, under the standing smallness hypothesis, the floor is inactive
(`contractionDen_eq`). -/
noncomputable def contractionDen (W : Graphon) (d : ℕ) (φ : ℝ → ℝ) : ℝ :=
  max (∫ x, contractionNum W d φ x ∂unitμ) (rStar d / 2)

/-- The **normalised contraction map** `N(φ) = T_W(φ^{d-1})/∫T_W(φ^{d-1})`, with the floored
denominator.  It is identically `1` when `W ≡ r_*`, which is why its derivative at the base
point vanishes and the iteration contracts. -/
noncomputable def contractionMap (W : Graphon) (d : ℕ) (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => contractionNum W d φ x / contractionDen W d φ

/-- The floor makes the denominator positive unconditionally. -/
theorem contractionDen_pos (hd : 2 ≤ d) : 0 < contractionDen W d φ :=
  lt_of_lt_of_le (half_pos (rStar_pos hd)) (le_max_right _ _)

/-- `contractionDen ≥ r_*/2`, again unconditionally. -/
theorem contractionDen_ge : rStar d / 2 ≤ contractionDen W d φ := le_max_right _ _

/-- `A(φ)` is measurable. -/
theorem measurable_contractionNum (hφ : ContractionMem d φ) : Measurable (contractionNum W d φ) :=
  measurable_kernelOp W.meas' hφ.measurable_pow

/-- `T_U(φ^{d-1})` is measurable. -/
theorem measurable_contractionErr (hφ : ContractionMem d φ) : Measurable (contractionErr W d φ) :=
  measurable_kernelOp (contraction_measurable_U W d) hφ.measurable_pow

/-- `N(φ)` is measurable. -/
theorem measurable_contractionMap (hφ : ContractionMem d φ) : Measurable (contractionMap W d φ) :=
  (measurable_contractionNum hφ).div_const _

/-- `A(φ) ≥ 0`, since `W ≥ 0` and `φ ≥ 0`. -/
theorem contractionNum_nonneg (hφ : ContractionMem d φ) (x : ℝ) : 0 ≤ contractionNum W d φ x := by
  simp only [contractionNum, kernelOp]
  exact integral_nonneg fun y => mul_nonneg (W.nonneg' x y) (pow_nonneg (hφ.nonneg y) _)

/-- `A(φ)(x) ≤ ∫φ^{d-1}`, since `W ≤ 1`. -/
theorem contractionNum_le (hd : 2 ≤ d) (hφ : ContractionMem d φ) (x : ℝ) :
    contractionNum W d φ x ≤ ∫ y, φ y ^ (d - 1) ∂unitμ := by
  simp only [contractionNum, kernelOp]
  refine integral_mono ?_ (hφ.integrable_pow hd) fun y => ?_
  · refine integrable_of_abs_le (W.meas'.of_uncurry_left.mul hφ.measurable_pow)
      (1 * contractionM d ^ (d - 1)) fun y => ?_
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩)
      (hφ.abs_pow_le hd y) (abs_nonneg _) zero_le_one
  · exact mul_le_of_le_one_left (pow_nonneg (hφ.nonneg y) _) (W.le_one' x y)

/-- `|T_U(φ^{d-1})| ≤ M^{d-1}`. -/
theorem abs_contractionErr_le (hd : 2 ≤ d) (hφ : ContractionMem d φ) (x : ℝ) :
    |contractionErr W d φ x| ≤ contractionM d ^ (d - 1) := by
  simpa [contractionErr] using abs_kernelOp_le (contraction_measurable_U W d) hφ.measurable_pow
    (contraction_abs_U_le hd W) (hφ.abs_pow_le hd) x

/-- `T_U(φ^{d-1})` is integrable. -/
theorem integrable_contractionErr (hd : 2 ≤ d) (hφ : ContractionMem d φ) :
    Integrable (contractionErr W d φ) unitμ :=
  integrable_of_abs_le (measurable_contractionErr hφ) _ (abs_contractionErr_le hd hφ)

/-! ## The `L⁴` estimates for `T_U` -/

/-- `‖T_U g‖₄ ≤ ε‖g‖₄`: `Lnorm_kernelOp_le` followed by `‖g‖_{4/3} ≤ ‖g‖₄`. -/
theorem contractionLnorm_kernelOp_U_le (hd : 2 ≤ d) (W : Graphon) {g : ℝ → ℝ} (hg : Measurable g)
    {Cg : ℝ} (hgb : ∀ y, |g y| ≤ Cg) :
    Lnorm unitμ 4 (kernelOp (contractionU W d) g) ≤ contractionEps W d * Lnorm unitμ 4 g := by
  refine le_trans (Lnorm_kernelOp_le (contraction_measurable_U W d) hg (contraction_abs_U_le hd W) hgb) ?_
  exact mul_le_mul_of_nonneg_left (Lnorm_43_le_Lnorm_4 hg hgb) (Lnorm_nonneg _ _ _)

/-- `|∫T_U g| ≤ ε‖g‖₄`: the mass defect of `T_U g` is `O(ε)` too. -/
theorem contraction_abs_integral_kernelOp_U_le (hd : 2 ≤ d) (W : Graphon) {g : ℝ → ℝ}
    (hg : Measurable g) {Cg : ℝ} (hgb : ∀ y, |g y| ≤ Cg) :
    |∫ x, kernelOp (contractionU W d) g x ∂unitμ| ≤ contractionEps W d * Lnorm unitμ 4 g := by
  have hb : ∀ x, |kernelOp (contractionU W d) g x| ≤ 1 * Cg :=
    abs_kernelOp_le (contraction_measurable_U W d) hg (contraction_abs_U_le hd W) hgb
  calc |∫ x, kernelOp (contractionU W d) g x ∂unitμ| ≤ ∫ x, |kernelOp (contractionU W d) g x| ∂unitμ :=
        abs_integral_le_integral_abs
    _ ≤ Lnorm unitμ 4 (kernelOp (contractionU W d) g) :=
        contractionIntegral_abs_le_Lnorm_four (measurable_kernelOp (contraction_measurable_U W d) hg) hb
    _ ≤ contractionEps W d * Lnorm unitμ 4 g := contractionLnorm_kernelOp_U_le hd W hg hgb

/-- `‖T_U(φ^{d-1})‖₄ ≤ εM^{d-1}`. -/
theorem Lnorm_contractionErr_le (hd : 2 ≤ d) (W : Graphon) (hφ : ContractionMem d φ) :
    Lnorm unitμ 4 (contractionErr W d φ) ≤ contractionEps W d * contractionM d ^ (d - 1) :=
  le_trans (contractionLnorm_kernelOp_U_le hd W hφ.measurable_pow (hφ.abs_pow_le hd))
    (mul_le_mul_of_nonneg_left (hφ.Lnorm_pow_le hd) (contractionEps_nonneg W d))

/-- `|∫T_U(φ^{d-1})| ≤ εM^{d-1}`. -/
theorem abs_integral_contractionErr_le (hd : 2 ≤ d) (W : Graphon) (hφ : ContractionMem d φ) :
    |∫ x, contractionErr W d φ x ∂unitμ| ≤ contractionEps W d * contractionM d ^ (d - 1) :=
  le_trans (contraction_abs_integral_kernelOp_U_le hd W hφ.measurable_pow (hφ.abs_pow_le hd))
    (mul_le_mul_of_nonneg_left (hφ.Lnorm_pow_le hd) (contractionEps_nonneg W d))

/-! ## Splitting off the rank-one part -/

/-- **The rank-one splitting of the numerator**,
`T_W(φ^{d-1})(x) = r_*∫φ^{d-1} + T_U(φ^{d-1})(x)`.

The first term does not depend on `x`.  This one line is why the normalised map has vanishing
first-order response at `W ≡ r_*`. -/
theorem contractionNum_split (hd : 2 ≤ d) (hφ : ContractionMem d φ) (x : ℝ) :
    contractionNum W d φ x = rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) + contractionErr W d φ x := by
  have hUm : Measurable fun y => contractionU W d x y := (contraction_measurable_U W d).of_uncurry_left
  have h2 : Integrable (fun y => contractionU W d x y * φ y ^ (d - 1)) unitμ := by
    refine integrable_of_abs_le (hUm.mul hφ.measurable_pow)
      (1 * contractionM d ^ (d - 1)) fun y => ?_
    rw [abs_mul]
    exact mul_le_mul (contraction_abs_U_le hd W x y) (hφ.abs_pow_le hd y) (abs_nonneg _) zero_le_one
  have key : ∀ y, W.toFun x y * φ y ^ (d - 1)
      = rStar d * φ y ^ (d - 1) + contractionU W d x y * φ y ^ (d - 1) := by
    intro y
    simp only [contractionU]
    ring
  simp only [contractionNum, contractionErr, kernelOp]
  calc ∫ y, W.toFun x y * φ y ^ (d - 1) ∂unitμ
      = ∫ y, (rStar d * φ y ^ (d - 1) + contractionU W d x y * φ y ^ (d - 1)) ∂unitμ :=
        integral_congr_ae (Filter.Eventually.of_forall key)
    _ = rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ)
          + ∫ y, contractionU W d x y * φ y ^ (d - 1) ∂unitμ := by
        rw [integral_add ((hφ.integrable_pow hd).const_mul _) h2, integral_const_mul]

/-- The integrated form of `contractionNum_split`. -/
theorem contractionNum_integral_split (hd : 2 ≤ d) (hφ : ContractionMem d φ) :
    ∫ x, contractionNum W d φ x ∂unitμ
      = rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) + ∫ x, contractionErr W d φ x ∂unitμ := by
  calc ∫ x, contractionNum W d φ x ∂unitμ
      = ∫ x, (rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) + contractionErr W d φ x) ∂unitμ :=
        integral_congr_ae (Filter.Eventually.of_forall (contractionNum_split hd hφ))
    _ = rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) + ∫ x, contractionErr W d φ x ∂unitμ := by
        rw [integral_add (integrable_const _) (integrable_contractionErr hd hφ), integral_const]
        simp

/-- The denominator is at least `r_*∫φ^{d-1}/2`: the rank-one term `r_*∫φ^{d-1} ≥ r_*` beats
the `O(ε)` defect. -/
theorem contractionNum_integral_lower (hd : 2 ≤ d) (hφ : ContractionMem d φ)
    (hε : contractionEps W d ≤ contractionEps0 d) :
    rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) / 2 ≤ ∫ x, contractionNum W d φ x ∂unitμ := by
  have hJ := hφ.one_le_integral_pow hd
  have hr := rStar_pos hd
  have hdef : |∫ x, contractionErr W d φ x ∂unitμ| ≤ rStar d / 2 :=
    le_trans (abs_integral_contractionErr_le hd W hφ) (contraction_eps_mul_le hd hε)
  have hlow := (abs_le.mp hdef).1
  have hmono : rStar d ≤ rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) :=
    le_mul_of_one_le_right hr.le hJ
  rw [contractionNum_integral_split hd hφ]
  linarith

/-- **The floor is inactive**: on `S`, under `ε ≤ ε₀`, `contractionDen` is the honest
`∫T_W(φ^{d-1})`. -/
theorem contractionDen_eq (hd : 2 ≤ d) (hφ : ContractionMem d φ) (hε : contractionEps W d ≤ contractionEps0 d) :
    contractionDen W d φ = ∫ x, contractionNum W d φ x ∂unitμ := by
  have hJ := hφ.one_le_integral_pow hd
  have hr := rStar_pos hd
  have h := contractionNum_integral_lower hd hφ hε
  have hmono : rStar d ≤ rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) :=
    le_mul_of_one_le_right hr.le hJ
  exact max_eq_left (by linarith)

/-! ## Estimate 1: the self-map property -/

/-- **Self-map.**  If `φ ∈ S` and `ε ≤ ε₀(d)` then `N(φ) ∈ S`: the iteration preserves
nonnegativity, the uniform bound `M = 2/r_*`, and unit mass.

The bound `N(φ) ≤ M` is where `M = 2/r_*` is forced: `A(φ) ≤ ∫φ^{d-1}` because `W ≤ 1`, while
`∫A(φ) ≥ r_*∫φ^{d-1}/2` by `contractionNum_integral_lower`. -/
theorem contractionMap_mem (hd : 2 ≤ d) (hφ : ContractionMem d φ) (hε : contractionEps W d ≤ contractionEps0 d) :
    ContractionMem d (contractionMap W d φ) := by
  have hDpos : 0 < contractionDen W d φ := contractionDen_pos hd
  have hDeq := contractionDen_eq hd hφ hε
  refine ⟨measurable_contractionMap hφ, fun x => div_nonneg (contractionNum_nonneg hφ x) hDpos.le,
    fun x => ?_, ?_⟩
  · rw [contractionMap, div_le_iff₀ hDpos]
    have h2 : rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) / 2 ≤ contractionDen W d φ := by
      rw [hDeq]; exact contractionNum_integral_lower hd hφ hε
    have h3 : contractionM d * (rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) / 2)
        = ∫ y, φ y ^ (d - 1) ∂unitμ := by
      linear_combination ((∫ y, φ y ^ (d - 1) ∂unitμ) / 2) * contractionM_mul_rStar hd
    calc contractionNum W d φ x ≤ ∫ y, φ y ^ (d - 1) ∂unitμ := contractionNum_le hd hφ x
      _ = contractionM d * (rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) / 2) := h3.symm
      _ ≤ contractionM d * contractionDen W d φ := mul_le_mul_of_nonneg_left h2 (contractionM_pos hd).le
  · simp only [contractionMap]
    rw [integral_div, ← hDeq, div_self hDpos.ne']

/-! ## Estimate 2: closeness to the constant `1` -/

/-- The pointwise form of the closeness estimate: on `S` the deviation of `N(φ)` from the
constant `1` is *exactly* the normalised deviation of `T_U(φ^{d-1})` from its own mean — the
rank-one constant `r_*∫φ^{d-1}` cancels between numerator and denominator. -/
theorem contractionMap_sub_one_eq (hd : 2 ≤ d) (hφ : ContractionMem d φ)
    (hε : contractionEps W d ≤ contractionEps0 d) (x : ℝ) :
    contractionMap W d φ x - 1
      = (contractionErr W d φ x - ∫ y, contractionErr W d φ y ∂unitμ) / contractionDen W d φ := by
  have hDpos : 0 < contractionDen W d φ := contractionDen_pos hd
  have h2 : contractionDen W d φ
      = rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ) + ∫ y, contractionErr W d φ y ∂unitμ := by
    rw [contractionDen_eq hd hφ hε]
    exact contractionNum_integral_split hd hφ
  rw [contractionMap, contractionNum_split hd hφ x]
  exact contraction_div_sub_one hDpos.ne' h2

/-- **Closeness, free and linear in `ε`.**  For *every* `φ` in the invariant set,

`‖N(φ) - 1‖₄ ≤ C_close(d)·ε`,  `C_close(d) = 2M^d = 4M^{d-1}/r_*`.

No small ball around a base point is needed: the constant parts of `T_W(φ^{d-1})` cancel in
`N(φ) - 1`, so the whole deviation is carried by `T_U`.  This is the raw-function precursor of
the `‖f - u_*‖₄ ≤ Cε` half of `eq:rank-one-reduction-bounds`. -/
theorem contractionMap_closeness (hd : 2 ≤ d) (hφ : ContractionMem d φ)
    (hε : contractionEps W d ≤ contractionEps0 d) :
    Lnorm unitμ 4 (fun x => contractionMap W d φ x - 1) ≤ contractionCloseConst d * contractionEps W d := by
  have hDpos : 0 < contractionDen W d φ := contractionDen_pos hd
  have hMk : (0 : ℝ) ≤ contractionM d ^ (d - 1) := pow_nonneg (contractionM_pos hd).le _
  have hEm : Measurable (contractionErr W d φ) := measurable_contractionErr hφ
  have hEb : ∀ x, |contractionErr W d φ x| ≤ contractionM d ^ (d - 1) := abs_contractionErr_le hd hφ
  have hie : |∫ y, contractionErr W d φ y ∂unitμ| ≤ contractionM d ^ (d - 1) := by
    calc |∫ y, contractionErr W d φ y ∂unitμ| ≤ ∫ y, |contractionErr W d φ y| ∂unitμ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _y : ℝ, contractionM d ^ (d - 1) ∂unitμ :=
          integral_mono (integrable_contractionErr hd hφ).abs (integrable_const _) hEb
      _ = contractionM d ^ (d - 1) := by simp
  have hgm : Measurable fun x => contractionErr W d φ x + -(∫ y, contractionErr W d φ y ∂unitμ) :=
    hEm.add_const _
  have hgb : ∀ x, |contractionErr W d φ x + -(∫ y, contractionErr W d φ y ∂unitμ)|
      ≤ 2 * contractionM d ^ (d - 1) := by
    intro x
    have h1 := hEb x
    calc |contractionErr W d φ x + -(∫ y, contractionErr W d φ y ∂unitμ)|
        ≤ |contractionErr W d φ x| + |-(∫ y, contractionErr W d φ y ∂unitμ)| := abs_add_le _ _
      _ ≤ 2 * contractionM d ^ (d - 1) := by rw [abs_neg]; linarith
  have hstep1 : Lnorm unitμ 4 (fun x => contractionMap W d φ x - 1)
      ≤ 1 / contractionDen W d φ
        * Lnorm unitμ 4 (fun x => contractionErr W d φ x + -(∫ y, contractionErr W d φ y ∂unitμ)) := by
    refine contractionLnorm_le_const_mul (by norm_num) (div_nonneg zero_le_one hDpos.le) hgm hgb
      fun x => ?_
    rw [contractionMap_sub_one_eq hd hφ hε x]
    have hform : contractionErr W d φ x - ∫ y, contractionErr W d φ y ∂unitμ
        = contractionErr W d φ x + -(∫ y, contractionErr W d φ y ∂unitμ) := by ring
    rw [hform, abs_div, abs_of_pos hDpos]
    exact le_of_eq (by ring)
  have hcb0 : ∀ _x : ℝ, |(-(∫ y, contractionErr W d φ y ∂unitμ))|
      ≤ |(-(∫ y, contractionErr W d φ y ∂unitμ))| := fun _ => le_refl _
  have hmink : Lnorm unitμ 4 (fun x => contractionErr W d φ x + -(∫ y, contractionErr W d φ y ∂unitμ))
      ≤ Lnorm unitμ 4 (contractionErr W d φ)
        + Lnorm unitμ 4 (fun _ : ℝ => -(∫ y, contractionErr W d φ y ∂unitμ)) :=
    contractionLnorm_add_le hEm measurable_const hEb hcb0
  have hconst : Lnorm unitμ 4 (fun _ : ℝ => -(∫ y, contractionErr W d φ y ∂unitμ))
      ≤ contractionEps W d * contractionM d ^ (d - 1) := by
    refine contractionLnorm_le (by norm_num)
      (mul_nonneg (contractionEps_nonneg W d) hMk) fun _ => ?_
    rw [abs_neg]
    exact abs_integral_contractionErr_le hd W hφ
  have hE4 := Lnorm_contractionErr_le hd W hφ
  have hstep2 : Lnorm unitμ 4 (fun x => contractionErr W d φ x + -(∫ y, contractionErr W d φ y ∂unitμ))
      ≤ 2 * (contractionEps W d * contractionM d ^ (d - 1)) := by linarith
  have h1D : 1 / contractionDen W d φ ≤ contractionM d := by
    have h := one_div_le_one_div_of_le (half_pos (rStar_pos hd))
      (contractionDen_ge (W := W) (φ := φ))
    rwa [one_div_div] at h
  have hfin : contractionM d * (2 * (contractionEps W d * contractionM d ^ (d - 1)))
      = contractionCloseConst d * contractionEps W d := by
    simp only [contractionCloseConst]
    rw [← contractionM_mul_pow hd]
    ring
  calc Lnorm unitμ 4 (fun x => contractionMap W d φ x - 1)
      ≤ 1 / contractionDen W d φ * Lnorm unitμ 4
          (fun x => contractionErr W d φ x + -(∫ y, contractionErr W d φ y ∂unitμ)) := hstep1
    _ ≤ contractionM d * Lnorm unitμ 4
          (fun x => contractionErr W d φ x + -(∫ y, contractionErr W d φ y ∂unitμ)) :=
        mul_le_mul_of_nonneg_right h1D (Lnorm_nonneg _ _ _)
    _ ≤ contractionM d * (2 * (contractionEps W d * contractionM d ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left hstep2 (contractionM_pos hd).le
    _ = contractionCloseConst d * contractionEps W d := hfin

/-! ## Estimate 3: the contraction -/

/-- Linearity of `T_U` in the second argument, for the two bounded measurable inputs at hand. -/
theorem contraction_kernelOp_sub (hd : 2 ≤ d) (W : Graphon) (hφ : ContractionMem d φ)
    (hψ : ContractionMem d ψ) (x : ℝ) :
    contractionErr W d φ x - contractionErr W d ψ x
      = kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) x := by
  have hUm : Measurable fun y => contractionU W d x y := (contraction_measurable_U W d).of_uncurry_left
  have hint : ∀ {χ : ℝ → ℝ}, ContractionMem d χ →
      Integrable (fun y => contractionU W d x y * χ y ^ (d - 1)) unitμ := by
    intro χ hχ
    refine integrable_of_abs_le (hUm.mul hχ.measurable_pow)
      (1 * contractionM d ^ (d - 1)) fun y => ?_
    rw [abs_mul]
    exact mul_le_mul (contraction_abs_U_le hd W x y) (hχ.abs_pow_le hd y) (abs_nonneg _) zero_le_one
  simp only [contractionErr, kernelOp]
  rw [← integral_sub (hint hφ) (hint hψ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

/-- The `L⁴` Lipschitz bound for `φ ↦ φ^{d-1}` on the invariant set,
`‖φ^{d-1} - ψ^{d-1}‖₄ ≤ L_d‖φ - ψ‖₄`, from `abs_pow_sub_pow_le_deg`. -/
theorem Lnorm_pow_sub_le (hd : 2 ≤ d) (hφ : ContractionMem d φ) (hψ : ContractionMem d ψ) :
    Lnorm unitμ 4 (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1))
      ≤ contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y) := by
  have hb : ∀ y, |φ y - ψ y| ≤ contractionM d := by
    intro y
    have h1 := hφ.nonneg y
    have h2 := hφ.le_bound y
    have h3 := hψ.nonneg y
    have h4 := hψ.le_bound y
    rw [abs_le]
    constructor <;> linarith
  exact contractionLnorm_le_const_mul (by norm_num) (contractionLip_nonneg hd) (hφ.meas.sub hψ.meas) hb
    fun y => abs_pow_sub_pow_le_deg hd (hφ.nonneg y) (hφ.le_bound y) (hψ.nonneg y)
      (hψ.le_bound y)

/-- **The contraction identity.**  With `c = r_*∫(φ^{d-1} - ψ^{d-1})` and
`e = T_U(φ^{d-1} - ψ^{d-1})`, for `φ, ψ ∈ S` and `ε ≤ ε₀(d)`,

`N(φ)(x) - N(ψ)(x) = (c(1 - N(ψ)(x)) + e(x) - N(ψ)(x)∫e) / ∫A(φ)`.

The denominator is `∫A(φ)`; and the first term is small because `1 - N(ψ)` is (by
`contractionMap_closeness`), *not* because `c` is — `c` is only `O(‖φ - ψ‖₄)`. -/
theorem contractionMap_sub_identity (hd : 2 ≤ d) (hφ : ContractionMem d φ) (hψ : ContractionMem d ψ)
    (hε : contractionEps W d ≤ contractionEps0 d) (x : ℝ) :
    contractionMap W d φ x - contractionMap W d ψ x
      = (rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ - ∫ y, ψ y ^ (d - 1) ∂unitμ)
            * (1 - contractionMap W d ψ x)
          + kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) x
          - contractionMap W d ψ x
            * ∫ z, kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) z ∂unitμ)
        / contractionDen W d φ := by
  have hDφ : 0 < contractionDen W d φ := contractionDen_pos hd
  have hDψ : 0 < contractionDen W d ψ := contractionDen_pos hd
  have hIe : ∫ z, kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) z ∂unitμ
      = (∫ z, contractionErr W d φ z ∂unitμ) - ∫ z, contractionErr W d ψ z ∂unitμ := by
    rw [← integral_sub (integrable_contractionErr hd hφ) (integrable_contractionErr hd hψ)]
    exact (integral_congr_ae
      (Filter.Eventually.of_forall (contraction_kernelOp_sub hd W hφ hψ))).symm
  have ha : contractionNum W d φ x
      = contractionNum W d ψ x
        + rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ - ∫ y, ψ y ^ (d - 1) ∂unitμ)
        + kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) x := by
    rw [contractionNum_split hd hφ x, contractionNum_split hd hψ x, ← contraction_kernelOp_sub hd W hφ hψ x]
    ring
  have hD : contractionDen W d φ
      = contractionDen W d ψ
        + rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ - ∫ y, ψ y ^ (d - 1) ∂unitμ)
        + ∫ z, kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) z ∂unitμ := by
    rw [contractionDen_eq hd hφ hε, contractionDen_eq hd hψ hε, contractionNum_integral_split hd hφ,
      contractionNum_integral_split hd hψ, hIe]
    ring
  simp only [contractionMap]
  exact contraction_quotient_identity hDφ.ne' hDψ.ne' hD ha

/-- **Contraction.**  For `φ, ψ ∈ S` and `ε ≤ ε₀(d)`,

`‖N(φ) - N(ψ)‖₄ ≤ C_contr(d)·ε·‖φ - ψ‖₄`,  `C_contr(d) = M(4M^{d-1} + 1 + M)L_d`.

Every term of the numerator in `contractionMap_sub_identity` is `O(ε)‖φ - ψ‖₄`: the first by
`contractionMap_closeness` (the small factor being `1 - N(ψ)`), the second and third by the operator
bound `contractionLnorm_kernelOp_U_le` together with `Lnorm_pow_sub_le`. -/
theorem contractionMap_contraction (hd : 2 ≤ d) (hφ : ContractionMem d φ) (hψ : ContractionMem d ψ)
    (hε : contractionEps W d ≤ contractionEps0 d) :
    Lnorm unitμ 4 (fun x => contractionMap W d φ x - contractionMap W d ψ x)
      ≤ contractionContrConst d * contractionEps W d * Lnorm unitμ 4 (fun y => φ y - ψ y) := by
  have hDφ : 0 < contractionDen W d φ := contractionDen_pos hd
  have hMpos := contractionM_pos hd
  have hEps := contractionEps_nonneg W d
  have hNψ : ContractionMem d (contractionMap W d ψ) := contractionMap_mem hd hψ hε
  have hδm : Measurable fun y => φ y ^ (d - 1) - ψ y ^ (d - 1) :=
    hφ.measurable_pow.sub hψ.measurable_pow
  have hδb : ∀ y, |φ y ^ (d - 1) - ψ y ^ (d - 1)| ≤ 2 * contractionM d ^ (d - 1) := by
    intro y
    have h1 := hφ.abs_pow_le hd y
    have h2 := hψ.abs_pow_le hd y
    exact le_trans contraction_abs_sub_le (by linarith)
  have hδL := Lnorm_pow_sub_le hd hφ hψ
  have hEm : Measurable (kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1))) :=
    measurable_kernelOp (contraction_measurable_U W d) hδm
  have hEb : ∀ x, |kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) x|
      ≤ 2 * contractionM d ^ (d - 1) := by
    intro x
    simpa using abs_kernelOp_le (contraction_measurable_U W d) hδm (contraction_abs_U_le hd W) hδb x
  have hEL : Lnorm unitμ 4 (kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)))
      ≤ contractionEps W d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y)) :=
    le_trans (contractionLnorm_kernelOp_U_le hd W hδm hδb) (mul_le_mul_of_nonneg_left hδL hEps)
  have hieL : |∫ z, kernelOp (contractionU W d)
        (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) z ∂unitμ|
      ≤ contractionEps W d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y)) :=
    le_trans (contraction_abs_integral_kernelOp_U_le hd W hδm hδb)
      (mul_le_mul_of_nonneg_left hδL hEps)
  have hieb : |∫ z, kernelOp (contractionU W d)
      (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) z ∂unitμ| ≤ 2 * contractionM d ^ (d - 1) := by
    calc |∫ z, kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) z ∂unitμ|
        ≤ ∫ z, |kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) z| ∂unitμ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _z : ℝ, 2 * contractionM d ^ (d - 1) ∂unitμ :=
          integral_mono (integrable_of_abs_le hEm _ hEb).abs (integrable_const _) hEb
      _ = 2 * contractionM d ^ (d - 1) := by simp
  have hc : |rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ - ∫ y, ψ y ^ (d - 1) ∂unitμ)|
      ≤ rStar d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y)) := by
    rw [abs_mul, abs_of_pos (rStar_pos hd)]
    refine mul_le_mul_of_nonneg_left ?_ (rStar_pos hd).le
    rw [← integral_sub (hφ.integrable_pow hd) (hψ.integrable_pow hd)]
    calc |∫ y, (φ y ^ (d - 1) - ψ y ^ (d - 1)) ∂unitμ|
        ≤ ∫ y, |φ y ^ (d - 1) - ψ y ^ (d - 1)| ∂unitμ := abs_integral_le_integral_abs
      _ ≤ Lnorm unitμ 4 (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) :=
          contractionIntegral_abs_le_Lnorm_four hδm hδb
      _ ≤ contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y) := hδL
  set c : ℝ := rStar d * (∫ y, φ y ^ (d - 1) ∂unitμ - ∫ y, ψ y ^ (d - 1) ∂unitμ) with hcdef
  set E : ℝ → ℝ := kernelOp (contractionU W d) (fun y => φ y ^ (d - 1) - ψ y ^ (d - 1)) with hEdef
  set ie : ℝ := ∫ z, E z ∂unitμ with hiedef
  -- the three numerator pieces
  have hT1m : Measurable fun x => contractionMap W d ψ x - 1 := (measurable_contractionMap hψ).sub_const _
  have hT1b : ∀ x, |contractionMap W d ψ x - 1| ≤ 1 + contractionM d := by
    intro x
    have h1 := hNψ.nonneg x
    have h2 := hNψ.le_bound x
    rw [abs_le]
    constructor <;> linarith
  have hT3m : Measurable fun x => -(contractionMap W d ψ x * ie) :=
    ((measurable_contractionMap hψ).mul_const _).neg
  have hb1 : ∀ x, |c * (1 - contractionMap W d ψ x)| ≤ |c| * (1 + contractionM d) := by
    intro x
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    rw [abs_sub_comm]
    exact hT1b x
  have hb3 : ∀ x, |-(contractionMap W d ψ x * ie)| ≤ contractionM d * (2 * contractionM d ^ (d - 1)) := by
    intro x
    rw [abs_neg, abs_mul]
    exact mul_le_mul (hNψ.abs_le hd x) hieb (abs_nonneg _) hMpos.le
  have hb23 : ∀ x, |E x + -(contractionMap W d ψ x * ie)|
      ≤ 2 * contractionM d ^ (d - 1) + contractionM d * (2 * contractionM d ^ (d - 1)) := fun x =>
    le_trans (abs_add_le _ _) (add_le_add (hEb x) (hb3 x))
  have hT1 : Lnorm unitμ 4 (fun x => c * (1 - contractionMap W d ψ x))
      ≤ 4 * contractionM d ^ (d - 1)
        * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y) * contractionEps W d) := by
    have hstep : Lnorm unitμ 4 (fun x => c * (1 - contractionMap W d ψ x))
        ≤ |c| * Lnorm unitμ 4 (fun x => contractionMap W d ψ x - 1) :=
      contractionLnorm_le_const_mul (by norm_num) (abs_nonneg c) hT1m hT1b fun x =>
        le_of_eq (by rw [abs_mul, abs_sub_comm (1 : ℝ) (contractionMap W d ψ x)])
    have h1 : |c| * Lnorm unitμ 4 (fun x => contractionMap W d ψ x - 1)
        ≤ |c| * (contractionCloseConst d * contractionEps W d) :=
      mul_le_mul_of_nonneg_left (contractionMap_closeness hd hψ hε) (abs_nonneg c)
    have h2 : |c| * (contractionCloseConst d * contractionEps W d)
        ≤ rStar d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y))
          * (contractionCloseConst d * contractionEps W d) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (contractionCloseConst_pos hd).le hEps)
    have h3 : rStar d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y))
          * (contractionCloseConst d * contractionEps W d)
        = 4 * contractionM d ^ (d - 1)
          * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y) * contractionEps W d) := by
      rw [← rStar_mul_contractionCloseConst hd]
      ring
    linarith
  have hT3 : Lnorm unitμ 4 (fun x => -(contractionMap W d ψ x * ie))
      ≤ contractionEps W d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y)) * contractionM d := by
    have hstep : Lnorm unitμ 4 (fun x => -(contractionMap W d ψ x * ie))
        ≤ |ie| * Lnorm unitμ 4 (contractionMap W d ψ) :=
      contractionLnorm_le_const_mul (by norm_num) (abs_nonneg ie) (measurable_contractionMap hψ)
        (hNψ.abs_le hd) fun x => le_of_eq (by rw [abs_neg, abs_mul, mul_comm])
    have h1 : Lnorm unitμ 4 (contractionMap W d ψ) ≤ contractionM d :=
      contractionLnorm_le (by norm_num) hMpos.le (hNψ.abs_le hd)
    have h2 : |ie| * Lnorm unitμ 4 (contractionMap W d ψ) ≤ |ie| * contractionM d :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg ie)
    have h3 : |ie| * contractionM d
        ≤ contractionEps W d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y)) * contractionM d :=
      mul_le_mul_of_nonneg_right hieL hMpos.le
    linarith
  have hsum2 : Lnorm unitμ 4 (fun x => E x + -(contractionMap W d ψ x * ie))
      ≤ Lnorm unitμ 4 E + Lnorm unitμ 4 (fun x => -(contractionMap W d ψ x * ie)) :=
    contractionLnorm_add_le hEm hT3m hEb hb3
  have hsum1 : Lnorm unitμ 4
      (fun x => c * (1 - contractionMap W d ψ x) + (E x + -(contractionMap W d ψ x * ie)))
      ≤ Lnorm unitμ 4 (fun x => c * (1 - contractionMap W d ψ x))
        + Lnorm unitμ 4 (fun x => E x + -(contractionMap W d ψ x * ie)) :=
    contractionLnorm_add_le ((measurable_const.sub (measurable_contractionMap hψ)).const_mul c)
      (hEm.add hT3m) hb1 hb23
  have hnum : Lnorm unitμ 4
      (fun x => c * (1 - contractionMap W d ψ x) + (E x + -(contractionMap W d ψ x * ie)))
      ≤ 4 * contractionM d ^ (d - 1)
          * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y) * contractionEps W d)
        + contractionEps W d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y))
        + contractionEps W d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y))
          * contractionM d := by linarith
  have hnm : Measurable fun x =>
      c * (1 - contractionMap W d ψ x) + (E x + -(contractionMap W d ψ x * ie)) :=
    ((measurable_const.sub (measurable_contractionMap hψ)).const_mul c).add (hEm.add hT3m)
  have hnb : ∀ x, |c * (1 - contractionMap W d ψ x) + (E x + -(contractionMap W d ψ x * ie))|
      ≤ |c| * (1 + contractionM d)
        + (2 * contractionM d ^ (d - 1) + contractionM d * (2 * contractionM d ^ (d - 1))) := fun x =>
    le_trans (abs_add_le _ _) (add_le_add (hb1 x) (hb23 x))
  have hid : ∀ x, contractionMap W d φ x - contractionMap W d ψ x
      = (c * (1 - contractionMap W d ψ x) + (E x + -(contractionMap W d ψ x * ie)))
        / contractionDen W d φ := by
    intro x
    rw [contractionMap_sub_identity hd hφ hψ hε x, hiedef, hEdef, hcdef]
    ring
  have hstep1 : Lnorm unitμ 4 (fun x => contractionMap W d φ x - contractionMap W d ψ x)
      ≤ 1 / contractionDen W d φ * Lnorm unitμ 4
          (fun x => c * (1 - contractionMap W d ψ x) + (E x + -(contractionMap W d ψ x * ie))) := by
    refine contractionLnorm_le_const_mul (by norm_num) (div_nonneg zero_le_one hDφ.le) hnm hnb
      fun x => ?_
    rw [hid x, abs_div, abs_of_pos hDφ]
    exact le_of_eq (by ring)
  have h1D : 1 / contractionDen W d φ ≤ contractionM d := by
    have h := one_div_le_one_div_of_le (half_pos (rStar_pos hd))
      (contractionDen_ge (W := W) (φ := φ))
    rwa [one_div_div] at h
  calc Lnorm unitμ 4 (fun x => contractionMap W d φ x - contractionMap W d ψ x)
      ≤ 1 / contractionDen W d φ * Lnorm unitμ 4
          (fun x => c * (1 - contractionMap W d ψ x) + (E x + -(contractionMap W d ψ x * ie))) := hstep1
    _ ≤ contractionM d * Lnorm unitμ 4
          (fun x => c * (1 - contractionMap W d ψ x) + (E x + -(contractionMap W d ψ x * ie))) :=
        mul_le_mul_of_nonneg_right h1D (Lnorm_nonneg _ _ _)
    _ ≤ contractionM d * (4 * contractionM d ^ (d - 1)
            * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y) * contractionEps W d)
          + contractionEps W d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y))
          + contractionEps W d * (contractionLip d * Lnorm unitμ 4 (fun y => φ y - ψ y))
            * contractionM d) := mul_le_mul_of_nonneg_left hnum hMpos.le
    _ = contractionContrConst d * contractionEps W d * Lnorm unitμ 4 (fun y => φ y - ψ y) := by
        simp only [contractionContrConst]
        ring

end SingularEndpoint

end UpperTailOptimizers
