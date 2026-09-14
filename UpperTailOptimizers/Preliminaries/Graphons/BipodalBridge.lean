import UpperTailOptimizers.Preliminaries.Graphons.Bipodal
import UpperTailOptimizers.Preliminaries.Graphons.HomDensity
import UpperTailOptimizers.Preliminaries.Graphons.ScalarEntropy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The two-block bipodal graphon and its edge, entropy and homomorphism densities

A *bipodal* graphon is determined by a measurable block `A ⊆ [0,1]` and three levels: `q₁₁` inside
`A`, `q₁₂` across, `q₂₂` outside.  `Preliminaries/Graphons/Bipodal.lean` gives the pointwise value
`bipodalValue A q₁₁ q₁₂ q₂₂`; this file packages it as a `Graphon` and computes the three functionals
the manuscript evaluates on it, in terms of the block measure `a = (unitμ A).toReal`:

* `bipodalGraphon_edgeDensity` — `Edge(W) = q₁₁a² + 2q₁₂a(1-a) + q₂₂(1-a)²`;
* `bipodalGraphon_entropy` — `Ent(W) = ½(H(q₁₁)a² + 2H(q₁₂)a(1-a) + H(q₂₂)(1-a)²)`, with `H` the
  Shannon entropy of `Preliminaries/Graphons/ScalarEntropy.lean` (the `Graphon.entropy` normalisation carries `-½∫`);
* `bipodalGraphon_tDensity_sum` — for *any* `H`, `t(H,W)` is the sum over block-labellings
  `τ : V(H) → Bool` of `(∏_{ab ∈ E(H)} B(τa,τb))·∏_v m(τ_v)`, with `B = blockVal` the level
  attached to a pair of blocks and `m = blockMeasure` the block measures.

These are the measure-theoretic identities behind every explicit bipodal computation in the
manuscript: the two-block reduction of `sec:local-reduction`, the quadratic upper bound of
`sec:nonexceptional-quadratic-growth` (`NonexceptionalEndpoint/QuadraticGrowth/BipodalUpper.lean`, `NonexceptionalEndpoint/QuadraticGrowth/QuadraticUpper.lean`), the
`t`-density expansion of `NonexceptionalEndpoint/QuadraticGrowth/TDensityExpansion.lean`, the chart of the KRR--S appendix
(`Preliminaries/KRRSAnalyticExtension/Chart.lean`), and the rank-one family of Section 5 (`SingularEndpoint/RankOneStationaryFamily/RankOne.lean`,
`SingularEndpoint/Proof/BipodalTransport.lean`).

Also here: `tDensity_congr_ae`, the a.e.-congruence of `t(H,·)` that lets each of the above be
proved for one representative and transported to any a.e.-equal graphon.
-/

namespace UpperTailOptimizers

open MeasureTheory Real
open scoped Classical

theorem bipodalValue_indicator_sum (A : Set ℝ) (q11 q12 q22 x y : ℝ) :
    bipodalValue A q11 q12 q22 (x, y)
      = q11 * (A.indicator 1 x * A.indicator 1 y)
        + q12 * (A.indicator 1 x * Aᶜ.indicator 1 y)
        + q12 * (Aᶜ.indicator 1 x * A.indicator 1 y)
        + q22 * (Aᶜ.indicator 1 x * Aᶜ.indicator 1 y) := by
  unfold bipodalValue
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
    simp [hx, hy, Set.mem_compl_iff]

/-- **Indicator decomposition of any function of the two-block value.** For any `φ`,
`φ(bipodalValue A q11 q12 q22 (x,y))` is `φ q11` on `A×A`, `φ q12` across, `φ q22` on `Aᶜ×Aᶜ`.
The `φ = id` case is `bipodalValue_indicator_sum`; `φ = entIntegrand` drives the entropy bridge. -/
theorem bipodalValue_comp_indicator_sum (φ : ℝ → ℝ) (A : Set ℝ) (q11 q12 q22 x y : ℝ) :
    φ (bipodalValue A q11 q12 q22 (x, y))
      = φ q11 * (A.indicator 1 x * A.indicator 1 y)
        + φ q12 * (A.indicator 1 x * Aᶜ.indicator 1 y)
        + φ q12 * (Aᶜ.indicator 1 x * A.indicator 1 y)
        + φ q22 * (Aᶜ.indicator 1 x * Aᶜ.indicator 1 y) := by
  unfold bipodalValue
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
    simp [hx, hy, Set.mem_compl_iff]

/-- **The concrete two-block bipodal graphon** with block `A` and edge probabilities
`q11` (inside `A`), `q12` (across), `q22` (outside `A`). This is `W(q,u,v,w)` of the two-block evaluation of the edge, entropy and `t`-densities
after relabelling the block to `A`, with `q11 = 1-u`, `q12 = v`, `q22 = w`. -/
noncomputable def bipodalGraphon (A : Set ℝ) (hA : MeasurableSet A) (q11 q12 q22 : ℝ)
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1) (h22 : q22 ∈ Set.Icc (0:ℝ) 1) :
    Graphon where
  toFun x y := bipodalValue A q11 q12 q22 (x, y)
  symm' x y := by
    unfold bipodalValue; dsimp only; split_ifs <;> rfl
  meas' := by
    have hsum : (Function.uncurry fun x y => bipodalValue A q11 q12 q22 (x, y))
        = fun z : ℝ × ℝ => q11 * (A.indicator 1 z.1 * A.indicator 1 z.2)
            + q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2)
            + q12 * (Aᶜ.indicator 1 z.1 * A.indicator 1 z.2)
            + q22 * (Aᶜ.indicator 1 z.1 * Aᶜ.indicator 1 z.2) := by
      funext z; exact bipodalValue_indicator_sum A q11 q12 q22 z.1 z.2
    rw [hsum]
    have mA : Measurable (A.indicator (1 : ℝ → ℝ)) := measurable_one.indicator hA
    have mAc : Measurable (Aᶜ.indicator (1 : ℝ → ℝ)) := measurable_one.indicator hA.compl
    exact (((((mA.comp measurable_fst).mul (mA.comp measurable_snd)).const_mul q11).add
          (((mA.comp measurable_fst).mul (mAc.comp measurable_snd)).const_mul q12)).add
        (((mAc.comp measurable_fst).mul (mA.comp measurable_snd)).const_mul q12)).add
        (((mAc.comp measurable_fst).mul (mAc.comp measurable_snd)).const_mul q22)
  nonneg' x y := by
    unfold bipodalValue; dsimp only; split_ifs
    · exact h11.1
    · exact h12.1
    · exact h12.1
    · exact h22.1
  le_one' x y := by
    unfold bipodalValue; dsimp only; split_ifs
    · exact h11.2
    · exact h12.2
    · exact h12.2
    · exact h22.2

@[simp] theorem bipodalGraphon_apply (A : Set ℝ) (hA : MeasurableSet A) (q11 q12 q22 : ℝ)
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1) (h22 : q22 ∈ Set.Icc (0:ℝ) 1)
    (x y : ℝ) :
    (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun x y = bipodalValue A q11 q12 q22 (x, y) :=
  rfl

/-- **Edge-density formula for the two-block bipodal graphon** (edge half of the two-block evaluation of the edge, entropy and `t`-densities). With
block measure `a := (unitμ A).toReal`,
`Edge(W) = q11·a² + q12·2a(1-a) + q22·(1-a)²`. -/
theorem bipodalGraphon_edgeDensity (A : Set ℝ) (hA : MeasurableSet A) (q11 q12 q22 : ℝ)
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1) (h22 : q22 ∈ Set.Icc (0:ℝ) 1) :
    (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).edgeDensity
      = q11 * (unitμ A).toReal ^ 2
        + q12 * (2 * (unitμ A).toReal * (1 - (unitμ A).toReal))
        + q22 * (1 - (unitμ A).toReal) ^ 2 := by
  show ∫ z, (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun z.1 z.2 ∂(unitμ.prod unitμ) = _
  -- rewrite the integrand into the indicator sum
  simp_rw [bipodalGraphon_apply, bipodalValue_indicator_sum]
  -- integrability of the four summands
  have hiA : Integrable (A.indicator (1 : ℝ → ℝ)) unitμ := (integrable_const 1).indicator hA
  have hiAc : Integrable (Aᶜ.indicator (1 : ℝ → ℝ)) unitμ := (integrable_const 1).indicator hA.compl
  have h1 : Integrable (fun z : ℝ × ℝ => q11 * (A.indicator 1 z.1 * A.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiA.mul_prod hiA).const_mul q11
  have h2 : Integrable (fun z : ℝ × ℝ => q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiA.mul_prod hiAc).const_mul q12
  have h3 : Integrable (fun z : ℝ × ℝ => q12 * (Aᶜ.indicator 1 z.1 * A.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiAc.mul_prod hiA).const_mul q12
  have h4 : Integrable (fun z : ℝ × ℝ => q22 * (Aᶜ.indicator 1 z.1 * Aᶜ.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiAc.mul_prod hiAc).const_mul q22
  have h12 : Integrable (fun z : ℝ × ℝ => q11 * (A.indicator 1 z.1 * A.indicator 1 z.2)
      + q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2)) (unitμ.prod unitμ) := h1.add h2
  have h123 : Integrable (fun z : ℝ × ℝ => q11 * (A.indicator 1 z.1 * A.indicator 1 z.2)
      + q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2)
      + q12 * (Aᶜ.indicator 1 z.1 * A.indicator 1 z.2)) (unitμ.prod unitμ) := h12.add h3
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2]
  simp only [integral_const_mul, integral_prod_mul]
  rw [integral_indicator_one hA, integral_indicator_one hA.compl]
  simp only [measureReal_def]
  have e3 : (unitμ Aᶜ).toReal = 1 - (unitμ A).toReal := by
    rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  rw [e3]; ring

/-- **Entropy formula for the two-block bipodal graphon** (entropy half of the two-block evaluation of the edge, entropy and `t`-densities). With
block measure `a := (unitμ A).toReal`,
`Ent(W) = ½·(H(q11)·a² + H(q12)·2a(1-a) + H(q22)·(1-a)²)`.

The blueprint states `Ent(W(q,u,v,w)) = S`; in the Lean normalisation `Graphon.entropy` carries a
`-½ ∫` factor, so this is the identity `Σ = bipS = -2·Ent` behind `Ip_eq_entropy`. -/
theorem bipodalGraphon_entropy (A : Set ℝ) (hA : MeasurableSet A) (q11 q12 q22 : ℝ)
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1) (h22 : q22 ∈ Set.Icc (0:ℝ) 1) :
    (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).entropy
      = (1 / 2) * (shannonH q11 * (unitμ A).toReal ^ 2
        + shannonH q12 * (2 * (unitμ A).toReal * (1 - (unitμ A).toReal))
        + shannonH q22 * (1 - (unitμ A).toReal) ^ 2) := by
  unfold Graphon.entropy
  rw [show gμ = unitμ.prod unitμ from rfl]
  -- the entropy integrand is `entIntegrand (W ·)`; decompose it over the four block cells
  rw [show (fun z : ℝ × ℝ => (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun z.1 z.2
        * Real.log ((bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun z.1 z.2)
        + (1 - (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun z.1 z.2)
          * Real.log (1 - (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun z.1 z.2))
      = (fun z : ℝ × ℝ => entIntegrand q11 * (A.indicator 1 z.1 * A.indicator 1 z.2)
          + entIntegrand q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2)
          + entIntegrand q12 * (Aᶜ.indicator 1 z.1 * A.indicator 1 z.2)
          + entIntegrand q22 * (Aᶜ.indicator 1 z.1 * Aᶜ.indicator 1 z.2))
      from by
        funext z
        show entIntegrand ((bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun z.1 z.2) = _
        rw [bipodalGraphon_apply]
        exact bipodalValue_comp_indicator_sum entIntegrand A q11 q12 q22 z.1 z.2]
  -- integrability of the four summands
  have hiA : Integrable (A.indicator (1 : ℝ → ℝ)) unitμ := (integrable_const 1).indicator hA
  have hiAc : Integrable (Aᶜ.indicator (1 : ℝ → ℝ)) unitμ := (integrable_const 1).indicator hA.compl
  have h1 : Integrable (fun z : ℝ × ℝ => entIntegrand q11 * (A.indicator 1 z.1 * A.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiA.mul_prod hiA).const_mul _
  have h2 : Integrable (fun z : ℝ × ℝ => entIntegrand q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiA.mul_prod hiAc).const_mul _
  have h3 : Integrable (fun z : ℝ × ℝ => entIntegrand q12 * (Aᶜ.indicator 1 z.1 * A.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiAc.mul_prod hiA).const_mul _
  have h4 : Integrable (fun z : ℝ × ℝ => entIntegrand q22 * (Aᶜ.indicator 1 z.1 * Aᶜ.indicator 1 z.2))
      (unitμ.prod unitμ) := (hiAc.mul_prod hiAc).const_mul _
  have h12 : Integrable (fun z : ℝ × ℝ => entIntegrand q11 * (A.indicator 1 z.1 * A.indicator 1 z.2)
      + entIntegrand q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2)) (unitμ.prod unitμ) := h1.add h2
  have h123 : Integrable (fun z : ℝ × ℝ => entIntegrand q11 * (A.indicator 1 z.1 * A.indicator 1 z.2)
      + entIntegrand q12 * (A.indicator 1 z.1 * Aᶜ.indicator 1 z.2)
      + entIntegrand q12 * (Aᶜ.indicator 1 z.1 * A.indicator 1 z.2)) (unitμ.prod unitμ) := h12.add h3
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2]
  simp only [integral_const_mul, integral_prod_mul]
  rw [integral_indicator_one hA, integral_indicator_one hA.compl]
  simp only [measureReal_def]
  have e3 : (unitμ Aᶜ).toReal = 1 - (unitμ A).toReal := by
    rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  rw [e3]
  simp only [entIntegrand_eq_neg_shannonH]
  ring

/-! ### The triangle identity `Tri = T` via the two-block labelling expansion.

The product-over-edges does *not* collapse to a product-over-vertices (as it did for the clique),
so we expand `t(H, W)` over the `2^{|V|}` block-labellings `τ : V → Bool` of the vertices
(the standard homomorphism-density-into-a-weighted-graph formula, restricted to two blocks). -/

/-- Block indicator: `1_A` for `true`, `1_{Aᶜ}` for `false`. -/
noncomputable def blockInd (A : Set ℝ) (b : Bool) (t : ℝ) : ℝ :=
  if b then A.indicator 1 t else Aᶜ.indicator 1 t

theorem blockInd_true (A : Set ℝ) (t : ℝ) : blockInd A true t = A.indicator 1 t := rfl
theorem blockInd_false (A : Set ℝ) (t : ℝ) : blockInd A false t = Aᶜ.indicator 1 t := rfl

/-- Two-block edge value as a function of the endpoints' blocks: `q11` (both in `A`),
`q12` (across), `q22` (both outside). -/
def blockVal (q11 q12 q22 : ℝ) (i j : Bool) : ℝ :=
  if i then (if j then q11 else q12) else (if j then q12 else q22)

theorem blockVal_symm (q11 q12 q22 : ℝ) (i j : Bool) :
    blockVal q11 q12 q22 i j = blockVal q11 q12 q22 j i := by
  cases i <;> cases j <;> rfl

/-- Block measure: `(unitμ A).toReal` for `true`, `(unitμ Aᶜ).toReal` for `false`. -/
noncomputable def blockMeasure (A : Set ℝ) (b : Bool) : ℝ :=
  if b then (unitμ A).toReal else (unitμ Aᶜ).toReal

theorem measurable_blockInd (A : Set ℝ) (hA : MeasurableSet A) (b : Bool) :
    Measurable (blockInd A b) := by
  cases b
  · show Measurable (Aᶜ.indicator (1 : ℝ → ℝ)); exact measurable_one.indicator hA.compl
  · show Measurable (A.indicator (1 : ℝ → ℝ)); exact measurable_one.indicator hA

theorem blockInd_mem_Icc (A : Set ℝ) (b : Bool) (t : ℝ) : blockInd A b t ∈ Set.Icc (0:ℝ) 1 := by
  have h : blockInd A b t = A.indicator 1 t ∨ blockInd A b t = Aᶜ.indicator 1 t := by
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl
  rcases h with h | h <;> rw [h, Set.indicator_apply] <;> split_ifs <;> simp [Set.mem_Icc]

theorem blockInd_self (A : Set ℝ) (t : ℝ) : blockInd A (decide (t ∈ A)) t = 1 := by
  by_cases h : t ∈ A
  · rw [decide_eq_true h, blockInd_true, Set.indicator_of_mem h]; rfl
  · rw [decide_eq_false h, blockInd_false, Set.indicator_of_mem (Set.mem_compl h)]; rfl

theorem blockInd_other (A : Set ℝ) {b : Bool} {t : ℝ} (h : b ≠ decide (t ∈ A)) :
    blockInd A b t = 0 := by
  by_cases ht : t ∈ A
  · have hb : b = false := by simpa [decide_eq_true ht] using h
    rw [hb, blockInd_false, Set.indicator_of_notMem (by simpa using ht)]
  · have hb : b = true := by simpa [decide_eq_false ht] using h
    rw [hb, blockInd_true, Set.indicator_of_notMem ht]

theorem bipodalValue_eq_blockVal (A : Set ℝ) (q11 q12 q22 x y : ℝ) :
    bipodalValue A q11 q12 q22 (x, y)
      = blockVal q11 q12 q22 (decide (x ∈ A)) (decide (y ∈ A)) := by
  unfold bipodalValue blockVal
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [hx, hy]

/-- `∫ blockInd A b = blockMeasure A b`. -/
theorem integral_blockInd (A : Set ℝ) (hA : MeasurableSet A) (b : Bool) :
    ∫ t, blockInd A b t ∂unitμ = blockMeasure A b := by
  cases b
  · show ∫ t, Aᶜ.indicator (1 : ℝ → ℝ) t ∂unitμ = _
    rw [integral_indicator_one hA.compl]; rfl
  · show ∫ t, A.indicator (1 : ℝ → ℝ) t ∂unitμ = _
    rw [integral_indicator_one hA]; rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`t(H,·)` depends only on the a.e. class** (a.e.-congruence of homomorphism density).
Generalises `tDensity_ae_const` from an a.e. constant to an arbitrary a.e.-equal graphon. -/
theorem tDensity_congr_ae {W W' : Graphon} (H : SimpleGraph V) [DecidableRel H.Adj]
    (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W'.toFun z.1 z.2) :
    W.tDensity H = W'.tDensity H := by
  have hedge : ∀ e ∈ H.edgeFinset, ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e
        = Sym2.lift ⟨fun a b => W'.toFun (x a) (x b), fun a b => W'.symm' (x a) (x b)⟩ e := by
    refine Sym2.ind (fun a b => ?_)
    intro he
    have hadj : H.Adj a b := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hpe := (measurePreserving_pair (V := V) hadj.ne).quasiMeasurePreserving.ae_eq hae
    filter_upwards [hpe] with x hx; exact hx
  have hall := (Filter.eventually_all_finset _).mpr hedge
  have hprod : ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      (∏ e ∈ H.edgeFinset, Sym2.lift
          ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e)
        = ∏ e ∈ H.edgeFinset, Sym2.lift
          ⟨fun a b => W'.toFun (x a) (x b), fun a b => W'.symm' (x a) (x b)⟩ e := by
    filter_upwards [hall] with x hx
    exact Finset.prod_congr rfl (fun e he => hx e he)
  unfold Graphon.tDensity
  exact integral_congr_ae hprod

/-- **Pointwise block-labelling expansion of the product over edges.** For a fixed vertex
assignment `x : V → ℝ`, the product over the edges of `H` of the two-block kernel equals the sum,
over all block-labellings `τ : V → Bool`, of `(∏_v 1_{block τv}(x v)) · ∏_e B(τ_a,τ_b)`. Only the
"true" labelling `τ v = (x v ∈ A)` survives (the others contribute a zero indicator). -/
theorem bipodalGraphon_prod_edges (A : Set ℝ) (hA : MeasurableSet A) (q11 q12 q22 : ℝ)
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1) (h22 : q22 ∈ Set.Icc (0:ℝ) 1)
    (H : SimpleGraph V) [DecidableRel H.Adj] (x : V → ℝ) :
    (∏ e ∈ H.edgeFinset, Sym2.lift
        ⟨fun a b => (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun (x a) (x b),
          fun a b => (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).symm' (x a) (x b)⟩ e)
      = ∑ τ : V → Bool, (∏ v, blockInd A (τ v) (x v))
          * ∏ e ∈ H.edgeFinset, Sym2.lift
              ⟨fun a b => blockVal q11 q12 q22 (τ a) (τ b),
                fun a b => blockVal_symm q11 q12 q22 (τ a) (τ b)⟩ e := by
  rw [Finset.sum_eq_single_of_mem (fun v => decide (x v ∈ A)) (Finset.mem_univ _)]
  · -- the surviving term equals the product over edges
    rw [Finset.prod_eq_one (fun v _ => blockInd_self A (x v)), one_mul]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    induction e using Sym2.ind with
    | _ a b => exact bipodalValue_eq_blockVal A q11 q12 q22 (x a) (x b)
  · -- every other labelling contributes a zero indicator
    intro τ _ hτ
    obtain ⟨v, hv⟩ : ∃ v, τ v ≠ decide (x v ∈ A) := by
      by_contra hcon; push Not at hcon; exact hτ (funext hcon)
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (blockInd_other A hv), zero_mul]

/-- **The two-block labelling formula for `t(H, ·)`** (the general step towards `Tri = T`). The
homomorphism density of `H` into the two-block bipodal graphon is the sum over block-labellings
`τ : V → Bool` of `(∏_e B(τ_a,τ_b)) · ∏_v m(τ_v)`, with block measures `m`. Holds for *any* `H`. -/
theorem bipodalGraphon_tDensity_sum (A : Set ℝ) (hA : MeasurableSet A) (q11 q12 q22 : ℝ)
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1) (h22 : q22 ∈ Set.Icc (0:ℝ) 1)
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).tDensity H
      = ∑ τ : V → Bool,
          (∏ e ∈ H.edgeFinset, Sym2.lift
            ⟨fun a b => blockVal q11 q12 q22 (τ a) (τ b),
              fun a b => blockVal_symm q11 q12 q22 (τ a) (τ b)⟩ e)
          * ∏ v, blockMeasure A (τ v) := by
  unfold Graphon.tDensity
  -- expand the integrand pointwise over the block-labellings
  simp_rw [bipodalGraphon_prod_edges A hA q11 q12 q22 h11 h12 h22 H]
  -- integrability of each labelling's summand
  have hint : ∀ τ : V → Bool,
      Integrable (fun x : V → ℝ => ∏ v, blockInd A (τ v) (x v)) (Measure.pi fun _ => unitμ) := by
    intro τ
    have hmeas : Measurable (fun x : V → ℝ => ∏ v, blockInd A (τ v) (x v)) :=
      Finset.measurable_prod _ (fun v _ => (measurable_blockInd A hA (τ v)).comp (measurable_pi_apply v))
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
    have h0 : 0 ≤ ∏ v, blockInd A (τ v) (x v) :=
      Finset.prod_nonneg (fun v _ => (blockInd_mem_Icc A (τ v) (x v)).1)
    have h1 : ∏ v, blockInd A (τ v) (x v) ≤ 1 :=
      Finset.prod_le_one (fun v _ => (blockInd_mem_Icc A (τ v) (x v)).1)
        (fun v _ => (blockInd_mem_Icc A (τ v) (x v)).2)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  -- interchange sum and integral, then Fubini over the vertices
  rw [integral_finsetSum Finset.univ (fun τ _ => (hint τ).mul_const _)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [integral_mul_const, integral_fintype_prod_eq_prod]
  simp_rw [integral_blockInd A hA]
  ring

/-! ### The block `A = [0,q]` -/

/-- `(unitμ [0,q]).toReal = q` for `q ∈ [0,1]`: the canonical block of prescribed measure. -/
theorem unitμ_Icc_toReal {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (unitμ (Set.Icc 0 q)).toReal = q := by
  rw [unitμ, Measure.restrict_apply measurableSet_Icc,
    show Set.Icc (0:ℝ) q ∩ Set.Icc 0 1 = Set.Icc 0 q by rw [Set.Icc_inter_Icc]; norm_num [hq1],
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring

end UpperTailOptimizers
