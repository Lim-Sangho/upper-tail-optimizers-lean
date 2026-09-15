import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.CdfTransport
import UpperTailOptimizers.Preliminaries.Graphons.BipodalBridge

/-!
# Relabelling a two-block graphon onto the standard blocks

The uniqueness clause of `thm:singular-endpoint` asserts that a minimiser agrees with the
family graphon `W_h` *up to relabelling*.  `W_h` is the two-block graphon whose vertex class is
the standard interval `Set.Icc 0 α_h`, whereas a minimiser produced by the comparison estimate
carries an arbitrary measurable class `A` of measure `α_h`.  This file closes that gap: the
measure-preserving map `σ = relabel A` of `CdfTransport.lean` carries `A` onto `[0,|A|]` almost
everywhere, hence carries the two-block value with class `A` onto the two-block value with the
standard class.

Nothing here is specific to the singular endpoint — it applies to any bipodal graphon, and is the
missing "normal form" statement behind `IsBipodal`.

## Contents

* `bipodalValue_comp_relabel` — the pointwise a.e. identity for `bipodalValue`;
* `bipodalGraphon_comp_relabel` — the same for `bipodalGraphon`;
* **`exists_relabel_eq_bipodalGraphon`** — any graphon that is a.e. two-block with class `A`
  equals the *standard* two-block graphon relabelled by a measure-preserving `σ`.
-/

namespace UpperTailOptimizers

open MeasureTheory


open scoped Classical

/-- **The two-block value is carried onto the standard blocks by `σ`.**  Immediate from
`relabel_mem_Icc_iff_mem_ae`, which says exactly that `σ` detects `A`. -/
theorem bipodalValue_comp_relabel {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Set.Icc 0 1)
    (q11 q12 q22 : ℝ) :
    ∀ᵐ z ∂gμ, bipodalValue A q11 q12 q22 z
      = bipodalValue (Set.Icc 0 (volume A).toReal) q11 q12 q22
          (relabel A z.1, relabel A z.2) := by
  filter_upwards [ae_gμ_of_ae_unitμ (relabel_mem_Icc_iff_mem_ae hA hAsub)] with z hz
  obtain ⟨h1, h2⟩ := hz
  unfold bipodalValue
  simp only [h1, h2]

/-- The graphon form of `bipodalValue_comp_relabel`. -/
theorem bipodalGraphon_comp_relabel {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Set.Icc 0 1)
    {α : ℝ} (hα : (volume A).toReal = α) {q11 q12 q22 : ℝ}
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1) (h22 : q22 ∈ Set.Icc (0:ℝ) 1) :
    ∀ᵐ z ∂gμ, (bipodalGraphon A hA q11 q12 q22 h11 h12 h22).toFun z.1 z.2
      = (bipodalGraphon (Set.Icc 0 α) measurableSet_Icc q11 q12 q22 h11 h12 h22).toFun
          (relabel A z.1) (relabel A z.2) := by
  subst hα
  exact bipodalValue_comp_relabel hA hAsub q11 q12 q22

/-- **Any a.e. two-block graphon is the standard two-block graphon, relabelled.**  This is the
normal form behind `IsBipodal`, and the shape in which the uniqueness clause of
`thm:singular-endpoint` wants its conclusion: a *single* measure-preserving `σ` of `[0,1]`
with `W(x,y) = W_std(σx, σy)` for `gμ`-a.e. `(x,y)`. -/
theorem exists_relabel_eq_bipodalGraphon {W : Graphon} {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Icc 0 1) {α : ℝ} (hα : (volume A).toReal = α) {q11 q12 q22 : ℝ}
    (h11 : q11 ∈ Set.Icc (0:ℝ) 1) (h12 : q12 ∈ Set.Icc (0:ℝ) 1) (h22 : q22 ∈ Set.Icc (0:ℝ) 1)
    (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue A q11 q12 q22 z) :
    ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
      ∀ᵐ z ∂gμ, W.toFun z.1 z.2
        = (bipodalGraphon (Set.Icc 0 α) measurableSet_Icc q11 q12 q22 h11 h12 h22).toFun
            (σ z.1) (σ z.2) := by
  refine ⟨relabel A, isRelabelling_relabel hA hAsub, ?_⟩
  filter_upwards [hW, bipodalGraphon_comp_relabel hA hAsub hα h11 h12 h22] with z hz hz'
  rw [hz]
  exact hz'

end UpperTailOptimizers
