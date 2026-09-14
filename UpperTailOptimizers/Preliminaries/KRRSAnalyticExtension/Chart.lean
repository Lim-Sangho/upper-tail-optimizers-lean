import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.TDensityExpansion
import UpperTailOptimizers.Preliminaries.Graphons.Attainment
import UpperTailOptimizers.LZBoundary.AnalyticIFT

/-!
# The bipodal parameter chart of Appendix B

Appendix B of `paper/paper.tex` works with the bipodal parameter
vector

`θ = (q₁₁, q₁₂, q₂₂, c)`,

`c` the size of the **first** pode, and the three functionals

`E(θ) = e(G_θ)`, `T_H(θ) = t(H, G_θ)`, and (implicitly) the entropy `s(G_θ)`.

This file sets up that chart and proves every bridge between it and the concrete graphon
layer, so that the reduced calculus of `Preliminaries/KRRSAnalyticExtension/Reduced.lean` onwards can be run purely in
θ-coordinates and the derivation in `Preliminaries/KRRSAnalyticExtension/Main.lean` never has to touch a measure-theoretic
argument.

## Coordinate convention

`Theta := ℝ × ℝ × ℝ × ℝ` with the order `(q₁₁, q₁₂, q₂₂, c)`.  This matches
`bipodalGraphon A hA q₁₁ q₁₂ q₂₂` (uncomplemented block densities) and
`tBip H a s q c` of `NonexceptionalEndpoint/QuadraticGrowth/TDensityExpansion.lean`.  It deliberately does **not**
use `bipodalGraphonIcc`/`bipE`/`bipT`, whose `(q,u,v,w)` chart carries the
*complement* `1-u` as the first internal density.

## Contents

* `bipEdge`, `bipTd`, `bipEnt` — the block formulas for `e`, `t(H,·)` and the entropy;
* `bipG` — the concrete graphon `G_θ` with the first pode normalised to `[0,c]`, and the
  three bridges `bipG_edgeDensity`, `bipG_tDensity`, `bipG_entropy`;
* `analyticAt_bipTd`, `tBip_zero` — analyticity of the `H`-density in the four parameters,
  and its value when the first pode is null (a constant graphon, so `q^m`);
* `entropy_congr_ae` — the entropy of a graphon depends only on its a.e. class;
* `bipodal_transfer` — the workhorse: it reads `e`, `t(H,·)` and the entropy off an
  *arbitrary relabelled* bipodal graphon.  Its three measure-theoretic ingredients — the
  product formula for the block measures, the identification of `bipTd` with the honest
  `H`-density, and the behaviour of `bipodalValue` under a relabelling — are file-private;
* `exists_rect` — extraction of a rectangle in `(ε, ϑ)` from a neighbourhood of `(ε₀, 0)`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

/-! ### The parameter chart -/

/-- The bipodal parameter vector `θ = (q₁₁, q₁₂, q₂₂, c)`, `c` the size of the first pode.
An `abbrev` so that the `NormedSpace ℝ` / `CompleteSpace` instances are found by
unification (needed to instantiate `analytic_inverse` at `E = Theta`). -/
abbrev Theta : Type := ℝ × ℝ × ℝ × ℝ

/-- `E(θ) = e(G_θ) = q₁₁ c² + q₁₂ · 2c(1-c) + q₂₂ (1-c)²`. -/
noncomputable def bipEdge (θ : Theta) : ℝ :=
  θ.1 * θ.2.2.2 ^ 2 + θ.2.1 * (2 * θ.2.2.2 * (1 - θ.2.2.2)) + θ.2.2.1 * (1 - θ.2.2.2) ^ 2

/-- `T_H(θ) = t(H, G_θ)`, as the labelling polynomial `tBip` of
`NonexceptionalEndpoint/QuadraticGrowth/TDensityExpansion.lean` (the construction for `lem:bipodal-quadratic-bound`). -/
noncomputable def bipTd {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (θ : Theta) : ℝ := tBip H θ.1 θ.2.1 θ.2.2.1 θ.2.2.2

/-- The block form of the entropy `s(G_θ)` (with the project's `-½∫` normalisation). -/
noncomputable def bipEnt (θ : Theta) : ℝ :=
  (1 / 2) * (shannonH θ.1 * θ.2.2.2 ^ 2
    + shannonH θ.2.1 * (2 * θ.2.2.2 * (1 - θ.2.2.2))
    + shannonH θ.2.2.1 * (1 - θ.2.2.2) ^ 2)

/-- **Fourth component of appendix item (b)**, proved: a bipodal graphon with a null first
pode is the constant graphon `q`, so its `H`-density is `q^m`.  Also the engine of the
`c ≠ 0` step of `Preliminaries/KRRSAnalyticExtension/Main.lean` (`c = 0` would force `τ = ε^m`). -/
theorem tBip_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q : ℝ) :
    tBip H a s q 0 = q ^ H.edgeFinset.card := by
  classical
  rw [tBip, Finset.sum_eq_single (fun _ : V => false)]
  · rw [edgeProd_const_false, trueCount_const_false, pow_zero, one_mul, Nat.sub_zero,
      sub_zero, one_pow, mul_one]
  · intro τ _ hτ
    have hne : trueCount τ ≠ 0 := fun h => hτ (label_eq_const_false h)
    rw [zero_pow hne, zero_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Analyticity of the chart functionals (appendix item (a), proved half) -/

/-- The first coordinate of a four-fold real product is analytic.  The names of these four
lemmas are deliberately role-neutral: downstream of `Preliminaries/KRRSAnalyticExtension/Reduced.lean` the same tuple
carries the appendix parameters `(ε,a,b,c)`, not `(q₁₁,q₁₂,q₂₂,c)`. -/
theorem analyticAt_fst4 (θ₀ : Theta) : AnalyticAt ℝ (fun θ : Theta => θ.1) θ₀ := analyticAt_fst

/-- The second coordinate of a four-fold real product is analytic. -/
theorem analyticAt_snd4 (θ₀ : Theta) : AnalyticAt ℝ (fun θ : Theta => θ.2.1) θ₀ :=
  analyticAt_fst.comp analyticAt_snd

/-- The third coordinate of a four-fold real product is analytic. -/
theorem analyticAt_thd4 (θ₀ : Theta) : AnalyticAt ℝ (fun θ : Theta => θ.2.2.1) θ₀ :=
  analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)

/-- The fourth coordinate of a four-fold real product is analytic. -/
theorem analyticAt_fth4 (θ₀ : Theta) : AnalyticAt ℝ (fun θ : Theta => θ.2.2.2) θ₀ :=
  analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)

/-- `T_H` is analytic (it is a polynomial in the four parameters). -/
theorem analyticAt_bipTd {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (θ₀ : Theta) : AnalyticAt ℝ (bipTd H) θ₀ := by
  classical
  have hbt : bipTd H = fun θ : Theta => tBip H θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 := rfl
  rw [hbt]
  simp only [tBip, edgeProd]
  refine Finset.analyticAt_fun_sum _ (fun τ _ => AnalyticAt.mul ?_ ?_)
  · refine Finset.analyticAt_fun_prod _ (fun e _ => ?_)
    induction e using Sym2.ind with
    | _ x y =>
      show AnalyticAt ℝ (fun θ : Theta => blockVal θ.1 θ.2.1 θ.2.2.1 (τ x) (τ y)) θ₀
      cases τ x <;> cases τ y <;>
        first
          | exact analyticAt_fst4 θ₀
          | exact analyticAt_snd4 θ₀
          | exact analyticAt_thd4 θ₀
  · exact ((analyticAt_fth4 θ₀).pow _).mul
      ((analyticAt_const.sub (analyticAt_fth4 θ₀)).pow _)

/-! ### The concrete graphon `G_θ` and the three bridges -/

/-- The bipodal graphon `G_θ` with the first pode normalised to `[0, c]`. -/
noncomputable def bipG (θ : Theta) (h11 : θ.1 ∈ Set.Icc (0:ℝ) 1)
    (h12 : θ.2.1 ∈ Set.Icc (0:ℝ) 1) (h22 : θ.2.2.1 ∈ Set.Icc (0:ℝ) 1) : Graphon :=
  bipodalGraphon (Set.Icc 0 θ.2.2.2) measurableSet_Icc θ.1 θ.2.1 θ.2.2.1 h11 h12 h22

theorem bipG_edgeDensity {θ : Theta} (h11 : θ.1 ∈ Set.Icc (0:ℝ) 1)
    (h12 : θ.2.1 ∈ Set.Icc (0:ℝ) 1) (h22 : θ.2.2.1 ∈ Set.Icc (0:ℝ) 1)
    (hc0 : 0 ≤ θ.2.2.2) (hc1 : θ.2.2.2 ≤ 1) :
    (bipG θ h11 h12 h22).edgeDensity = bipEdge θ := by
  rw [bipG, bipodalGraphon_edgeDensity, unitμ_Icc_toReal hc0 hc1]
  unfold bipEdge; ring

theorem bipG_entropy {θ : Theta} (h11 : θ.1 ∈ Set.Icc (0:ℝ) 1)
    (h12 : θ.2.1 ∈ Set.Icc (0:ℝ) 1) (h22 : θ.2.2.1 ∈ Set.Icc (0:ℝ) 1)
    (hc0 : 0 ≤ θ.2.2.2) (hc1 : θ.2.2.2 ≤ 1) :
    (bipG θ h11 h12 h22).entropy = bipEnt θ := by
  rw [bipG, bipodalGraphon_entropy, unitμ_Icc_toReal hc0 hc1]
  unfold bipEnt; ring

theorem bipG_tDensity {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {θ : Theta} (h11 : θ.1 ∈ Set.Icc (0:ℝ) 1)
    (h12 : θ.2.1 ∈ Set.Icc (0:ℝ) 1) (h22 : θ.2.2.1 ∈ Set.Icc (0:ℝ) 1)
    (hc0 : 0 ≤ θ.2.2.2) (hc1 : θ.2.2.2 ≤ 1) :
    (bipG θ h11 h12 h22).tDensity H = bipTd H θ :=
  tBip_eq_tDensity H h11 h12 h22 hc0 hc1

/-! ### Evaluating the chart on an arbitrary relabelled bipodal graphon -/

/-- Relabelling a two-block value by `σ` is the same as taking the two-block value on the
preimage block. -/
private theorem bipodalValue_comp (A : Set ℝ) (q11 q12 q22 : ℝ) (σ : ℝ → ℝ) (x y : ℝ) :
    bipodalValue A q11 q12 q22 (σ x, σ y)
      = bipodalValue (σ ⁻¹' A) q11 q12 q22 (x, y) := by
  unfold bipodalValue
  by_cases hx : σ x ∈ A <;> by_cases hy : σ y ∈ A <;>
    simp [hx, hy, Set.mem_preimage]

/-- **The entropy depends only on the a.e. class** (companion of
`tDensity_congr_ae` and `edgeDensity_congr_ae`). -/
theorem entropy_congr_ae {W W' : Graphon}
    (h : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W'.toFun z.1 z.2) : W.entropy = W'.entropy := by
  unfold Graphon.entropy
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with z hz
  rw [hz]

/-- The block-measure product for an *arbitrary* measurable block of measure `c`
(`prod_blockMeasure_Icc` is the case `A = [0,c]`). -/
private theorem prod_blockMeasure_eq {V : Type*} [Fintype V] {A : Set ℝ} (hA : MeasurableSet A)
    {c : ℝ} (hc : (unitμ A).toReal = c) (τ : V → Bool) :
    (∏ v, blockMeasure A (τ v))
      = c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ) := by
  classical
  have hbm : ∀ b : Bool, blockMeasure A b = if b = true then c else 1 - c := by
    intro b
    cases b
    · show (unitμ Aᶜ).toReal = _
      rw [prob_compl_eq_one_sub hA,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, hc]
      simp
    · show (unitμ A).toReal = _
      rw [hc]; simp
  have hτc : trueCount τ = (Finset.univ.filter fun v => τ v = true).card := rfl
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (fun v => τ v = true)
  rw [Finset.card_univ] at hsum
  calc (∏ v, blockMeasure A (τ v))
      = ∏ v, (if τ v = true then c else 1 - c) := Finset.prod_congr rfl fun v _ => hbm (τ v)
    _ = (∏ _v ∈ Finset.univ.filter fun v => τ v = true, c)
        * ∏ _v ∈ Finset.univ.filter fun v => ¬ τ v = true, (1 - c) := Finset.prod_ite _ _
    _ = c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ) := by
        rw [Finset.prod_const, Finset.prod_const, hτc]
        congr 2
        omega

/-- **`t(H, ·) = tBip`** for a two-block graphon on an *arbitrary* measurable block of
measure `c` (`tBip_eq_tDensity` is the case `A = [0,c]`).  This is what evaluates `T_H` on
the relabelled maximizer supplied by the localizing axiom. -/
private theorem tBip_eq_tDensity_of_measure {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {A : Set ℝ} (hA : MeasurableSet A) {a s q c : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (hc : (unitμ A).toReal = c) :
    (bipodalGraphon A hA a s q ha hs hq).tDensity H = tBip H a s q c := by
  rw [bipodalGraphon_tDensity_sum, tBip]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [prod_blockMeasure_eq hA hc τ, edgeProd]

/-- **Transfer of the three functionals to a relabelled two-block graphon.**  If `W` agrees
a.e. with the two-block kernel of parameters `θ` composed with a measure-preserving
relabelling `σ`, then its edge density, `H`-density and entropy are the block formulas
`bipEdge θ`, `bipTd H θ`, `bipEnt θ`.

This is what lets the derivation read the chart off an arbitrary bipodal maximizer — such as
the one produced in `Preliminaries/KRRSBipodality/Bipodal.lean` — with no measure-isomorphism argument: the
relabelled block `σ⁻¹(A)` has the same measure as `A`. -/
theorem bipodal_transfer {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {θ : Theta} (h11 : θ.1 ∈ Set.Icc (0:ℝ) 1)
    (h12 : θ.2.1 ∈ Set.Icc (0:ℝ) 1) (h22 : θ.2.2.1 ∈ Set.Icc (0:ℝ) 1)
    (hc : θ.2.2.2 ∈ Set.Icc (0:ℝ) 1) {σ : ℝ → ℝ} (hσ : IsRelabelling σ)
    {W : Graphon}
    (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2
      = bipodalValue (Set.Icc 0 θ.2.2.2) θ.1 θ.2.1 θ.2.2.1 (σ z.1, σ z.2)) :
    W.edgeDensity = bipEdge θ ∧ W.tDensity H = bipTd H θ ∧ W.entropy = bipEnt θ := by
  classical
  have hA : MeasurableSet (σ ⁻¹' (Set.Icc 0 θ.2.2.2)) := hσ.measurable measurableSet_Icc
  have hmeas : (unitμ (σ ⁻¹' (Set.Icc 0 θ.2.2.2))).toReal = θ.2.2.2 := by
    rw [hσ.measurePreserving.measure_preimage measurableSet_Icc.nullMeasurableSet, unitμ_Icc_toReal hc.1 hc.2]
  have hWG : ∀ᵐ z ∂gμ, W.toFun z.1 z.2
      = (bipodalGraphon (σ ⁻¹' (Set.Icc 0 θ.2.2.2)) hA θ.1 θ.2.1 θ.2.2.1
          h11 h12 h22).toFun z.1 z.2 := by
    filter_upwards [hae] with z hz
    rw [hz, bipodalGraphon_apply]
    exact bipodalValue_comp _ _ _ _ σ z.1 z.2
  refine ⟨?_, ?_, ?_⟩
  · rw [edgeDensity_congr_ae hWG, bipodalGraphon_edgeDensity, hmeas]
    unfold bipEdge; ring
  · rw [tDensity_congr_ae H hWG, tBip_eq_tDensity_of_measure H hA h11 h12 h22 hmeas]
    rfl
  · rw [entropy_congr_ae hWG, bipodalGraphon_entropy, hmeas]
    unfold bipEnt; ring

/-! ### The rectangle extraction -/

/-- **Extraction of a rectangle in `(ε, ϑ)`** from a neighbourhood of `(x₀, 0)` — the
appendix's step (A.IFT-rectangle). -/
theorem exists_rect {P : ℝ → ℝ → Prop} {x₀ : ℝ}
    (h : ∀ᶠ p in 𝓝 (x₀, (0:ℝ)), P p.1 p.2) :
    ∃ a Δ : ℝ, 0 < a ∧ 0 < Δ ∧ ∀ x, |x - x₀| < a → ∀ y, |y| < Δ → P x y := by
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at h
  obtain ⟨pa, hpa, pb, hpb, hP⟩ := h
  rw [Metric.eventually_nhds_iff] at hpa hpb
  obtain ⟨a, ha, hpa'⟩ := hpa
  obtain ⟨Δ, hΔ, hpb'⟩ := hpb
  refine ⟨a, Δ, ha, hΔ, fun x hx y hy => ?_⟩
  refine hP (hpa' ?_) (hpb' ?_)
  · rwa [Real.dist_eq]
  · rw [Real.dist_eq, sub_zero]; exact hy

end UpperTailOptimizers
