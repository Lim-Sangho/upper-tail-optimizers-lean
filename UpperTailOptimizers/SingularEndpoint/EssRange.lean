import UpperTailOptimizers.SingularEndpoint.TwoValued

/-!
# The essential range of a rank-one KKT factor (Section 7)

This file closes `lem:stationary-rank-one-bipodality` of `paper/singular_endpoint.tex`.  Two ingredients
are already in place.  `SingularEndpoint.four_zeros_absurd` (`SingularEndpoint/Bipodality.lean`) says the
rank-one KKT function `F_{p,γ}(z) = J_p'(z) - γ z^{d-1}` has at most three zeros in `(0,1)`,
and `SingularEndpoint.not_three_values` (`SingularEndpoint/TwoValued.lean`) says a rank-one KKT *factor*
`f` cannot take three distinct values each on a set of positive `unitμ`-measure.  What is
still missing is the essential-range step: passing from "no three values of positive
measure" to "`f` is almost everywhere two-valued".

The passage has three steps, matching the three theorems below.

* *The zero set is finite.*  A four-element subset of `{z ∈ (0,1) | F_{p,γ}(z) = 0}` can be
  listed in increasing order and fed to `four_zeros_absurd`, so no such subset exists and
  the zero set cannot be infinite.
* *`f` has finite essential range.*  Since `gμ = unitμ.prod unitμ`, the a.e. statement
  `F_{p,γ}(f(x)f(y)) = 0` disintegrates (`MeasureTheory.Measure.ae_ae_of_ae_prod`) into
  "for a.e. `x`, for a.e. `y`".  `unitμ` is a probability measure, so a witness `x₀` of the
  outer statement exists; for a.e. `y` the product `f(x₀)f(y)` then lies in the zero set of
  the previous step, whence `f(y)` lies in its image under division by `f(x₀)`.
* *The essential range has at most two points.*  Discard from that finite set the values
  whose level set is null — a finite union of null sets — and what remains is a finite set
  `T` all of whose points are genuinely attained on positive measure.  If `T` had three
  points, its minimum, that third point and its maximum would be three values of positive
  measure, contradicting `not_three_values`; so `T ⊆ {min T, max T}`.

## Contents

* `finite_fkkt_zeros` — the zero set of `F_{p,γ}` in `(0,1)` is finite;
* `ae_mem_finite_of_kkt` — a rank-one KKT factor lies a.e. in a finite set;
* `exists_two_values` — **`lem:stationary-rank-one-bipodality`, final form**: a rank-one KKT factor
  is almost everywhere equal to one of two constants.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

variable {d : ℕ}

/-! ## The zero set is finite -/

/-- **`eq:rank-one-kkt`, root count, in set form.**

The rank-one KKT function `F_{p,γ}` has only finitely many zeros in the open unit interval.
Indeed an infinite zero set would contain a four-element `Finset`; listing it in increasing
order via `Finset.orderEmbOfFin` produces `z₁ < z₂ < z₃ < z₄` in `(0,1)` with
`F_{p,γ}(zᵢ) = 0`, which `SingularEndpoint.four_zeros_absurd` forbids. -/
theorem finite_fkkt_zeros (hd : 2 ≤ d) {p g : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    {z : ℝ | z ∈ Set.Ioo (0:ℝ) 1 ∧ Fkkt d p g z = 0}.Finite := by
  by_contra hinf
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf 4
  have hmem : ∀ i : Fin 4,
      t.orderEmbOfFin htc i ∈ {z : ℝ | z ∈ Set.Ioo (0:ℝ) 1 ∧ Fkkt d p g z = 0} :=
    fun i => hts (Finset.orderEmbOfFin_mem t htc i)
  have hmono : StrictMono (t.orderEmbOfFin htc) := (t.orderEmbOfFin htc).strictMono
  exact four_zeros_absurd hd hp0 hp1 (hmem 0).1.1
    (hmono (show (0 : Fin 4) < 1 by decide))
    (hmono (show (1 : Fin 4) < 2 by decide))
    (hmono (show (2 : Fin 4) < 3 by decide))
    (hmem 3).1.2 (hmem 0).2 (hmem 1).2 (hmem 2).2 (hmem 3).2

/-! ## The factor has finite essential range -/

/-- **`lem:stationary-rank-one-bipodality`, the Fubini step.**

If `F_{p,γ}(f(x)f(y)) = 0` for `gμ`-a.e. `(x, y)` and `f` takes values in `(0,1)`, then `f`
lies almost everywhere in a *finite* set of reals: fix a point `x₀` for which the equation
holds for a.e. `y`, and divide the (finite) zero set of `F_{p,γ}` by `f(x₀)`.  This is the
sentence "By Fubini's theorem, one can choose `y₀` …" of the paper's proof. -/
theorem ae_mem_finite_of_kkt (hd : 2 ≤ d) {p g : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {f : ℝ → ℝ} (_hfm : Measurable f) (hpos : ∀ x, 0 < f x) (hlt : ∀ x, f x < 1)
    (hkkt : ∀ᵐ z ∂gμ, Fkkt d p g (f z.1 * f z.2) = 0) :
    ∃ S : Set ℝ, S.Finite ∧ ∀ᵐ x ∂unitμ, f x ∈ S := by
  have hZ : {z : ℝ | z ∈ Set.Ioo (0:ℝ) 1 ∧ Fkkt d p g z = 0}.Finite :=
    finite_fkkt_zeros hd hp0 hp1
  have hkkt' : ∀ᵐ z ∂(unitμ.prod unitμ), Fkkt d p g (f z.1 * f z.2) = 0 := by
    rw [← gμ]; exact hkkt
  have hprod : ∀ᵐ x ∂unitμ, ∀ᵐ y ∂unitμ, Fkkt d p g (f x * f y) = 0 :=
    Measure.ae_ae_of_ae_prod hkkt'
  obtain ⟨x₀, hx₀⟩ := hprod.exists
  refine ⟨(fun w => w / f x₀) '' {z : ℝ | z ∈ Set.Ioo (0:ℝ) 1 ∧ Fkkt d p g z = 0},
    hZ.image _, ?_⟩
  filter_upwards [hx₀] with y hy
  refine ⟨f x₀ * f y, ⟨⟨mul_pos (hpos x₀) (hpos y), ?_⟩, hy⟩, ?_⟩
  · nlinarith [hpos x₀, hpos y, hlt x₀, hlt y]
  · exact mul_div_cancel_left₀ _ (hpos x₀).ne'

/-! ## The conclusion: two values -/

/-- **`lem:stationary-rank-one-bipodality`, final form.**

A measurable `f : [0,1] → (0,1)` satisfying the rank-one KKT equation
`F_{p,γ}(f(x)f(y)) = 0` for `gμ`-a.e. `(x, y)` is almost everywhere equal to one of two
constants.  Combined with `SingularEndpoint.ae_mem_finite_of_kkt`, which confines `f` to a finite
set `S`, this is the essential-range argument: the values in `S` carried by a null level set
contribute a null set in total, and the remaining values cannot number three by
`SingularEndpoint.not_three_values`, so the minimum and the maximum of what remains already exhaust
them.  Together with `f` not a.e. constant this gives the paper's `f = a·1_B + b·1_{B^c}`. -/
theorem exists_two_values (hd : 2 ≤ d) {p g : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {f : ℝ → ℝ} (hfm : Measurable f) (hpos : ∀ x, 0 < f x) (hlt : ∀ x, f x < 1)
    (hkkt : ∀ᵐ z ∂gμ, Fkkt d p g (f z.1 * f z.2) = 0) :
    ∃ a b : ℝ, ∀ᵐ x ∂unitμ, f x = a ∨ f x = b := by
  obtain ⟨S, hSfin, hSae⟩ := ae_mem_finite_of_kkt hd hp0 hp1 hfm hpos hlt hkkt
  -- the values of `S` whose level set is not null
  set T : Set ℝ := {v | v ∈ S ∧ unitμ {x | f x = v} ≠ 0} with hTdef
  have hTfin : T.Finite := hSfin.subset fun v hv => hv.1
  -- discarding the null level sets discards a null set
  have hNfin : {v | v ∈ S ∧ unitμ {x | f x = v} = 0}.Finite := hSfin.subset fun v hv => hv.1
  have hnull : unitμ (⋃ v ∈ {v | v ∈ S ∧ unitμ {x | f x = v} = 0}, {x | f x = v}) = 0 :=
    (measure_biUnion_null_iff hNfin.countable).mpr fun _ hv => hv.2
  have hae2 : ∀ᵐ x ∂unitμ, ¬ (f x ∈ S ∧ unitμ {y | f y = f x} = 0) := by
    rw [ae_iff]
    simp only [not_not]
    refine measure_mono_null ?_ hnull
    rintro x ⟨hx1, hx2⟩
    exact Set.mem_biUnion (show f x ∈ _ from ⟨hx1, hx2⟩) rfl
  have hTae : ∀ᵐ x ∂unitμ, f x ∈ T := by
    filter_upwards [hSae, hae2] with x hx1 hx2
    exact ⟨hx1, fun hx3 => hx2 ⟨hx1, hx3⟩⟩
  -- every point of `T` is a genuine value of `f`, hence lies in `(0,1)`
  have hTval : ∀ v ∈ T, 0 < v ∧ v < 1 ∧ 0 < unitμ {x | f x = v} := by
    intro v hv
    obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hv.2
    exact ⟨hx₀ ▸ hpos x₀, hx₀ ▸ hlt x₀, pos_iff_ne_zero.mpr hv.2⟩
  rcases hTfin.toFinset.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨0, 0, ?_⟩
    filter_upwards [hTae] with x hx
    exact absurd (hFe ▸ hTfin.mem_toFinset.mpr hx) (Finset.notMem_empty _)
  · refine ⟨hTfin.toFinset.min' hFne, hTfin.toFinset.max' hFne, ?_⟩
    filter_upwards [hTae] with x hx
    by_contra hcon
    push Not at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    have hxF : f x ∈ hTfin.toFinset := hTfin.mem_toFinset.mpr hx
    have hmin : hTfin.toFinset.min' hFne < f x :=
      lt_of_le_of_ne (hTfin.toFinset.min'_le _ hxF) (Ne.symm hne1)
    have hmax : f x < hTfin.toFinset.max' hFne :=
      lt_of_le_of_ne (hTfin.toFinset.le_max' _ hxF) hne2
    have hminT : hTfin.toFinset.min' hFne ∈ T :=
      hTfin.mem_toFinset.mp (hTfin.toFinset.min'_mem hFne)
    have hmaxT : hTfin.toFinset.max' hFne ∈ T :=
      hTfin.mem_toFinset.mp (hTfin.toFinset.max'_mem hFne)
    exact not_three_values hd hp0 hp1 hfm hkkt (hTval _ hminT).1 hmin hmax
      (hTval _ hmaxT).2.1 (hTval _ hminT).2.2 (hTval _ hx).2.2 (hTval _ hmaxT).2.2

end SingularEndpoint

end UpperTailOptimizers
