import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.EssRange
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.PowFirstOrder
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.RankOne

/-!
# Graphon stationarity: `eq:graphon-stationarity` and `eq:block-stationarity`

Section 5 of `paper/paper.tex` states its first-order conditions variationally.  `W` is
*stationary* for `I_p - μ t(H,·)` when

  `d/dε|_{ε=0} [ I_p(W + εU) - μ t(H, W + εU) ] = 0`   (`eq:graphon-stationarity`)

for every bounded symmetric `U`, and a rank-one `W = f⊗f` *satisfies the KKT conditions* at
`(p,r)` with multiplier `μ` when this holds with `μ ≥ 0` and `t(H,W) = r^m`.  The block
proportion carries its own condition, because moving the boundary between the two vertex classes
is not a small perturbation in `L^∞`:

  `d/dβ|_{β=α} [ I_p(W_{β,s,t}) - μ t(H, W_{β,s,t}) ] = 0`   (`eq:block-stationarity`).

This file introduces `eq:graphon-stationarity` together with the ambient objects it needs, and
computes the `I_p` half of the first variation.  `SingularEndpoint/RankOneStationaryFamily/StationaryVariation.lean`
computes the `t(H,·)` half; `SingularEndpoint/RankOneStationaryFamily/StationaryReduction.lean` defines
`eq:block-stationarity` and carries out the reduction to the scalar equations the rest of
Section 5 uses.

## Kernels rather than graphons

`W + εU` is a graphon only for `|ε|` small, and only under the interiority hypothesis
`η ≤ f ≤ 1-η` that the paper imposes for exactly this reason.  Rather than carry that proof
obligation inside the definition, the two functionals are defined on **symmetric measurable
kernels** (`SymKernel`), of which graphons are the ones with values in `[0,1]`:
`SymKernel.Ip` and `SymKernel.tDensity` restrict to `Graphon.Ip` and `Graphon.tDensity`
(`graphonKernel_Ip`, `graphonKernel_tDensity`).  Since `HasDerivAt _ _ 0` sees only the
germ at `ε = 0`, and the perturbed kernel *is* a graphon near `ε = 0` under interiority, this
agrees with the paper's condition.

## Contents

* `SymKernel`, `Direction`, `graphonKernel`, `SymKernel.pert` — the kernels, the bounded
  symmetric directions `U`, and the perturbation `W + εU`;
* `SymKernel.Ip`, `SymKernel.tDensity`, with `graphonKernel_Ip`, `graphonKernel_tDensity`;
* `IsStationary`, `SatisfiesKKT` — `eq:graphon-stationarity` and the KKT conditions;
* `hasDerivAt_Ip_pert` — the first variation of `I_p`:
  `d/dε|₀ I_p(W+εU) = ∬ J_p'(W) U`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Filter Topology

/-! ## Kernels and directions -/

/-- A symmetric measurable kernel on `[0,1]²`.  A graphon is one whose values lie in `[0,1]`;
the perturbations `W + εU` of `eq:graphon-stationarity` are kernels of this kind. -/
structure SymKernel where
  /-- The underlying function. -/
  toFun : ℝ → ℝ → ℝ
  symm' : ∀ x y, toFun x y = toFun y x
  meas' : Measurable fun z : ℝ × ℝ => toFun z.1 z.2

/-- A **direction** for testing stationarity: a bounded symmetric measurable `U`, exactly the
class `eq:graphon-stationarity` quantifies over. -/
structure Direction extends SymKernel where
  /-- A uniform bound on `|U|`. -/
  bound : ℝ
  bound_ge : ∀ x y, |toFun x y| ≤ bound

/-- Every graphon is a symmetric measurable kernel. -/
def graphonKernel (W : Graphon) : SymKernel where
  toFun := W.toFun
  symm' := W.symm'
  meas' := W.measurable_uncurry

namespace SymKernel

/-- The relative-entropy functional on a kernel, `I_p(w) = ∫∫ J_p(w)`. -/
noncomputable def Ip (w : SymKernel) (p : ℝ) : ℝ := ∫ z, Jp p (w.toFun z.1 z.2) ∂gμ

/-- The homomorphism density on a kernel, `t(H,w)`. -/
noncomputable def tDensity (w : SymKernel) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : ℝ :=
  ∫ x : V → ℝ,
    ∏ e ∈ H.edgeFinset, Sym2.lift ⟨fun a b => w.toFun (x a) (x b), fun a b => w.symm' (x a) (x b)⟩ e
    ∂(Measure.pi fun _ => unitμ)

/-- The perturbed kernel `w + εU`. -/
def pert (w : SymKernel) (U : Direction) (ε : ℝ) : SymKernel where
  toFun x y := w.toFun x y + ε * U.toFun x y
  symm' x y := by rw [w.symm', U.symm']
  meas' := w.meas'.add (measurable_const.mul U.meas')

@[simp] theorem pert_toFun (w : SymKernel) (U : Direction) (ε : ℝ) (x y : ℝ) :
    (w.pert U ε).toFun x y = w.toFun x y + ε * U.toFun x y := rfl

@[simp] theorem pert_zero (w : SymKernel) (U : Direction) : w.pert U 0 = w := by
  cases w; simp [pert]

end SymKernel

@[simp] theorem graphonKernel_Ip (W : Graphon) (p : ℝ) : (graphonKernel W).Ip p = W.Ip p := rfl

@[simp] theorem graphonKernel_tDensity (W : Graphon) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : (graphonKernel W).tDensity H = W.tDensity H := rfl

/-! ## The two stationarity conditions -/

/-- **`eq:graphon-stationarity`.**  `W` is stationary for `I_p - μ t(H,·)` when

  `d/dε|_{ε=0} [I_p(W + εU) - μ t(H, W + εU)] = 0`

for every bounded symmetric `U`. -/
def IsStationary {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (p μ : ℝ) (W : Graphon) : Prop :=
  ∀ U : Direction, HasDerivAt
    (fun ε : ℝ => ((graphonKernel W).pert U ε).Ip p - μ * ((graphonKernel W).pert U ε).tDensity H) 0 0

/-- **The KKT conditions at `(p,r)` with multiplier `μ`**: stationarity
(`eq:graphon-stationarity`) together with `μ ≥ 0` and the density constraint `t(H,W) = r^m`. -/
def SatisfiesKKT {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (p r μ : ℝ) (W : Graphon) : Prop :=
  0 ≤ μ ∧ W.tDensity H = r ^ H.edgeFinset.card ∧ IsStationary H p μ W

/-! ## The first variation of `I_p` -/

/-- `J_p'` is measurable. -/
theorem measurable_Jp' (p : ℝ) : Measurable (Jp' p) :=
  Real.measurable_log.comp ((measurable_id.mul measurable_const).div
    ((measurable_const.sub measurable_id).mul measurable_const))

/-- **The interiority window.**  If `η ≤ W ≤ 1-η` then `W + εU` stays inside
`[η/2, 1-η/2] ⊂ (0,1)` for `|ε| < η/(2(|U.bound|+1))`.  This is the role of the paper's
hypothesis `η ≤ f ≤ 1-η`: it makes `W + εU` a graphon, so stationarity can be tested in every
bounded direction. -/
theorem pert_mem_Icc {W : Graphon} {U : Direction} {η : ℝ} (hη : 0 < η)
    (hW0 : ∀ x y, η ≤ W.toFun x y) (hW1 : ∀ x y, W.toFun x y ≤ 1 - η)
    {ε : ℝ} (hε : |ε| < η / (2 * (|U.bound| + 1))) (x y : ℝ) :
    W.toFun x y + ε * U.toFun x y ∈ Set.Icc (η / 2) (1 - η / 2) := by
  have hb0 : (0 : ℝ) < |U.bound| + 1 := by positivity
  have habs : |ε * U.toFun x y| ≤ |ε| * (|U.bound| + 1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (le_trans (le_trans (U.bound_ge x y) (le_abs_self _)) (by linarith)) (abs_nonneg ε)
  have hlt : |ε| * (|U.bound| + 1) < η / 2 := by
    have := mul_lt_mul_of_pos_right hε hb0
    calc |ε| * (|U.bound| + 1) < η / (2 * (|U.bound| + 1)) * (|U.bound| + 1) := this
      _ = η / 2 := by field_simp
  have h1 := (abs_le.mp (le_trans habs hlt.le)).1
  have h2 := (abs_le.mp (le_trans habs hlt.le)).2
  exact ⟨by linarith [hW0 x y], by linarith [hW1 x y]⟩

/-- **The first variation of `I_p`** (`lem:stationary-rank-one-bipodality`, the display for
`d/dε I_p(W_ε)`):

  `d/dε|_{ε=0} I_p(W + εU) = ∬ J_p'(W(x,y)) U(x,y) dx dy`.

Differentiation under the integral sign: on the window where `W + εU` stays in
`[η/2, 1-η/2]`, the `ε`-derivative `J_p'(W+εU)·U` is bounded by a constant
(`abs_Jp'_le`), which is integrable because `gμ` is a probability measure. -/
theorem hasDerivAt_Ip_pert (W : Graphon) (U : Direction) {p η : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hη : 0 < η) (hW0 : ∀ x y, η ≤ W.toFun x y)
    (hW1 : ∀ x y, W.toFun x y ≤ 1 - η) :
    HasDerivAt (fun ε : ℝ => ((graphonKernel W).pert U ε).Ip p)
      (∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ) 0 := by
  classical
  set δ : ℝ := η / (2 * (|U.bound| + 1)) with hδdef
  have hb0 : (0 : ℝ) < |U.bound| + 1 := by positivity
  have hδ : 0 < δ := by rw [hδdef]; positivity
  set F : ℝ → ℝ × ℝ → ℝ := fun ε z => Jp p (W.toFun z.1 z.2 + ε * U.toFun z.1 z.2) with hF
  set F' : ℝ → ℝ × ℝ → ℝ :=
    fun ε z => Jp' p (W.toFun z.1 z.2 + ε * U.toFun z.1 z.2) * U.toFun z.1 z.2 with hF'
  set s : Set ℝ := Metric.ball (0 : ℝ) δ with hs
  have hsmem : s ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hδ
  have hmemIcc : ∀ ε ∈ s, ∀ z : ℝ × ℝ,
      W.toFun z.1 z.2 + ε * U.toFun z.1 z.2 ∈ Set.Icc (η / 2) (1 - η / 2) := by
    intro ε hε z
    have : |ε| < δ := by simpa [hs, Real.dist_eq] using hε
    exact pert_mem_Icc hη hW0 hW1 this z.1 z.2
  -- measurability
  have hmeasW : Measurable fun z : ℝ × ℝ => W.toFun z.1 z.2 := W.measurable_uncurry
  have hmeasF : ∀ ε : ℝ, Measurable (F ε) := fun ε =>
    (measurable_Jp p).comp (hmeasW.add (measurable_const.mul U.meas'))
  have hmeasF' : ∀ ε : ℝ, Measurable (F' ε) := fun ε =>
    ((measurable_Jp' p).comp (hmeasW.add (measurable_const.mul U.meas'))).mul U.meas'
  -- the constant bound on the derivative
  have hηhalf0 : (0 : ℝ) < η / 2 := by linarith
  have hηhalf1 : (1 : ℝ) - η / 2 < 1 := by linarith
  set C : ℝ := (|ell p| + (|Real.log (η / 2)| + |Real.log (1 - (1 - η / 2))|))
    * (|U.bound| + 1) with hC
  have hbound : ∀ ε ∈ s, ∀ z : ℝ × ℝ, ‖F' ε z‖ ≤ C := by
    intro ε hε z
    have hz := hmemIcc ε hε z
    have h1 := abs_Jp'_le hp0 hp1 hηhalf0 hηhalf1 hz
    have h2 : |U.toFun z.1 z.2| ≤ |U.bound| + 1 :=
      le_trans (le_trans (U.bound_ge z.1 z.2) (le_abs_self _)) (by linarith)
    have hnn : (0 : ℝ) ≤ |ell p| + (|Real.log (η / 2)| + |Real.log (1 - (1 - η / 2))|) := by
      positivity
    rw [Real.norm_eq_abs, hF', abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hnn
  -- integrability of the base integrand
  obtain ⟨CJ, hCJ⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_Jp_Icc hp0 hp1)
  have hFint : Integrable (F 0) gμ := by
    refine integrable_of_abs_le (hmeasF 0) CJ (fun z => ?_)
    have : W.toFun z.1 z.2 + (0 : ℝ) * U.toFun z.1 z.2 = W.toFun z.1 z.2 := by ring
    rw [hF]
    simp only [this]
    simpa [Real.norm_eq_abs] using hCJ _ (W.mem_Icc z.1 z.2)
  -- the pointwise derivative
  have hdiff : ∀ z : ℝ × ℝ, ∀ ε ∈ s, HasDerivAt (fun ε : ℝ => F ε z) (F' ε z) ε := by
    intro z ε hε
    have hz := hmemIcc ε hε z
    have hz0 : 0 < W.toFun z.1 z.2 + ε * U.toFun z.1 z.2 := lt_of_lt_of_le hηhalf0 hz.1
    have hz1 : W.toFun z.1 z.2 + ε * U.toFun z.1 z.2 < 1 := lt_of_le_of_lt hz.2 hηhalf1
    have hinner : HasDerivAt (fun ε : ℝ => W.toFun z.1 z.2 + ε * U.toFun z.1 z.2)
        (U.toFun z.1 z.2) ε := by
      simpa using ((hasDerivAt_id ε).mul_const (U.toFun z.1 z.2)).const_add (W.toFun z.1 z.2)
    exact (hasDerivAt_Jp hp0 hp1 hz0 hz1).comp ε hinner
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (bound := fun _ => C) (μ := gμ) hsmem
    (Eventually.of_forall fun ε => (hmeasF ε).aestronglyMeasurable) hFint
    (hmeasF' 0).aestronglyMeasurable
    (Eventually.of_forall fun z => fun ε hε => hbound ε hε z)
    (integrable_const C)
    (Eventually.of_forall fun z => hdiff z)
  have hzero : ∀ z : ℝ × ℝ, F' 0 z = Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 := by
    intro z; rw [hF']; norm_num
  rw [show (fun z : ℝ × ℝ => Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2) = F' 0 from
    (funext hzero).symm]
  exact hkey.2

end SingularEndpoint

end UpperTailOptimizers
