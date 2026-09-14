import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.AnalyticExcess

/-!
# `thm:positive-second-variation`: one analytic extension over a neighbourhood of `K × {0}`

`boundaryExcess_chart` (`NonexceptionalEndpoint/QuadraticGrowth/AnalyticExcess.lean`) extends the boundary excess across
`δ = 0` **near one density** `r₀`: it returns a box `|r - r₀| < w`, `|δ| ≤ ρ` and a function `Gc`
analytic there, agreeing with `G_r(δ)` on the half-box `0 < δ < ρ`.
`thm:positive-second-variation` of `paper/paper.tex` states a **single** real-analytic `G` on an
open set `𝒩` containing `I × (-δ̄, δ̄)`, where `I ∋ r₀` is an open interval that the paper shrinks
until one analytic parameter map of `thm:krrs-analytic-extension` covers it.  This file proves the
statement over an arbitrary compact `K` of nonexceptional densities on a boundary arc, which gives
the paper's form with `K` the closure of `I`.  Over such a `K` a single chart need not suffice, so
the local charts are glued with the identity theorem.

Two charts overlap in a set `Ioo a b ×ˢ Ioo (-ρ) ρ`, which is convex, hence preconnected; on its
upper half both charts equal `boundaryExcess`, an open set of agreement.  So
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` makes them agree on the whole overlap, and a
finite subcover of `K` glues the charts into one `G`.

Note that `AH` is *not* defined through the extension here: it is the chart-independent right
limit `lim_{δ↓0} 2G_r(δ)/δ²` of `NonexceptionalEndpoint/QuadraticGrowth/AnalyticExcess.lean`, and the extension is proved
to have it as its second `δ`-derivative at `δ = 0`.  Where the paper *defines*
`A_H(r) := ∂²_δG(r,0)`, the Lean statement asserts that equality.

## Contents

* `eqOn_prod_Ioo_of_eventuallyEq` — the identity theorem on a product of intervals;
* `boundaryExcess_extension` — the glued extension: the neighbourhood `𝒩`, the analytic `G`,
  `eq:boundary-excess-extension`, clause (i), and clause (iii) with a constant depending only
  on `K`;
* `positive_second_variation` — `thm:positive-second-variation` in full, adding clauses (ii)
  and (iv) from `boundaryExcess_taylor`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set Filter Topology

/-- **The identity theorem on a box.**  Two functions analytic on `Ioo a b ×ˢ Ioo c d` that agree
near one of its points agree on all of it: the box is convex, hence preconnected. -/
theorem eqOn_prod_Ioo_of_eventuallyEq {f g : ℝ × ℝ → ℝ} {a b c e : ℝ}
    (hf : ∀ p ∈ Set.Ioo a b ×ˢ Set.Ioo c e, AnalyticAt ℝ f p)
    (hg : ∀ p ∈ Set.Ioo a b ×ˢ Set.Ioo c e, AnalyticAt ℝ g p)
    {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ Set.Ioo a b ×ˢ Set.Ioo c e) (h : f =ᶠ[𝓝 p₀] g) :
    Set.EqOn f g (Set.Ioo a b ×ˢ Set.Ioo c e) :=
  AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg
    ((convex_Ioo a b).prod (convex_Ioo c e)).isPreconnected hp₀ h

/-- **`thm:positive-second-variation`, the extension clause.**  For a compact `K` of
non-exceptional densities on a Lubetzky–Zhao boundary arc there are `δ̄ > 0`, a constant `C₂`
depending only on `K`, an open `𝒩 ⊇ K × (-δ̄, δ̄)` and a real-analytic `G : 𝒩 → ℝ` with

* `G(r,δ) = G_r(δ)` for `r ∈ K`, `0 < δ < δ̄`  (`eq:boundary-excess-extension`);
* `G(r,0) = 0` and `∂_δG(r,0) = 0` for `r ∈ K`  (clause (i));
* `∂²_δG(r,0) = A_H(r)`, and `|∂²_δG(r,δ) - A_H(r)| ≤ C₂|δ|` for `r ∈ K`, `|δ| < δ̄`
  (clause (iii)).

The single `G` is obtained by patching the local charts of `boundaryExcess_chart` over a finite
subcover of `K`; it depends on that subcover, and any two choices agree on the common domain by
the same identity-theorem argument used to build them. -/
theorem boundaryExcess_extension {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKex : ∀ r ∈ K, r ≠ rStar d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ (δbar C₂ : ℝ) (N : Set (ℝ × ℝ)) (G : ℝ × ℝ → ℝ),
      0 < δbar ∧ 0 ≤ C₂ ∧ IsOpen N ∧
      (∀ r ∈ K, ∀ δ : ℝ, |δ| < δbar → (r, δ) ∈ N) ∧
      (∀ p ∈ N, AnalyticAt ℝ G p) ∧
      (∀ p ∈ N, AnalyticAt ℝ (dDelta G) p) ∧
      (∀ r ∈ K, ∀ δ : ℝ, 0 < δ → δ < δbar → G (r, δ) = boundaryExcess H M r δ) ∧
      (∀ r ∈ K, G (r, 0) = 0) ∧
      (∀ r ∈ K, dDelta G (r, 0) = 0) ∧
      (∀ r ∈ K, dDelta (dDelta G) (r, 0) = AH H M r) ∧
      (∀ r ∈ K, ∀ δ : ℝ, |δ| < δbar →
        |dDelta (dDelta G) (r, δ) - AH H M r| ≤ C₂ * |δ|) := by
  classical
  -- a chart at every point of `K`
  have hchart : ∀ r₀ ∈ K, ∃ w ρ Mc : ℝ, 0 < w ∧ 0 < ρ ∧ 0 ≤ Mc ∧ ∃ Gc : ℝ × ℝ → ℝ,
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ → AnalyticAt ℝ Gc (r, δ)) ∧
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ → AnalyticAt ℝ (dDelta Gc) (r, δ)) ∧
      (∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρ → boundaryExcess H M r δ = Gc (r, δ)) ∧
      (∀ r : ℝ, |r - r₀| < w → Gc (r, 0) = 0) ∧
      (∀ r : ℝ, |r - r₀| < w → dDelta Gc (r, 0) = 0) ∧
      (∀ r : ℝ, |r - r₀| < w → dDelta (dDelta Gc) (r, 0) = AH H M r) ∧
      (∀ r δ : ℝ, |r - r₀| < w → |δ| ≤ ρ →
        |dDelta (dDelta Gc) (r, δ) - AH H M r| ≤ Mc * |δ|) ∧
      (∀ r δ : ℝ, |r - r₀| < w → 0 < δ → δ < ρ →
        |boundaryExcess H M r δ - AH H M r * δ ^ 2 / 2| ≤ Mc * δ ^ 3) := fun r₀ hr₀ =>
    boundaryExcess_chart hd M H hreg hm (hK hr₀) (hKex r₀ hr₀)
  choose! w ρ Mc hw hρ hMc Gc hA1 hA2 hAgree hZ0 hZ1 hZ2 hCurv _hCubic using hchart
  -- a finite subcover of `K` by the chart windows
  set I : ℝ → Set ℝ := fun i => Set.Ioo (i - w i) (i + w i) with hIdef
  have hmem : ∀ i r : ℝ, r ∈ I i ↔ |r - i| < w i := by
    intro i r
    rw [hIdef]
    simp only [Set.mem_Ioo, abs_lt]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hcov : K ⊆ ⋃ i ∈ K, I i := by
    intro r hr
    exact Set.mem_biUnion hr ((hmem r r).mpr (by simpa using hw r hr))
  obtain ⟨S, hSK, hSfin, hScov⟩ :=
    hKc.elim_finite_subcover_image (fun i _ => isOpen_Ioo) hcov
  -- the finite subcover is nonempty
  obtain ⟨r₁, hr₁⟩ := hKne
  have hSne : S.Nonempty := by
    obtain ⟨s, hs, -⟩ := Set.mem_iUnion₂.mp (hScov hr₁)
    exact ⟨s, hs⟩
  set T : Finset ℝ := hSfin.toFinset with hTdef
  have hTmem : ∀ i : ℝ, i ∈ T ↔ i ∈ S := by intro i; rw [hTdef]; simp
  have hTne : T.Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    exact ⟨s, (hTmem s).mpr hs⟩
  set δbar : ℝ := T.inf' hTne ρ with hδdef
  set C₂ : ℝ := T.sup' hTne Mc with hCdef
  have hδpos : 0 < δbar := by
    rw [hδdef, Finset.lt_inf'_iff]
    exact fun i hi => hρ i (hSK ((hTmem i).mp hi))
  have hδle : ∀ i ∈ S, δbar ≤ ρ i := fun i hi => Finset.inf'_le _ ((hTmem i).mpr hi)
  have hCle : ∀ i ∈ S, Mc i ≤ C₂ := fun i hi => Finset.le_sup' _ ((hTmem i).mpr hi)
  have hC0 : 0 ≤ C₂ := by
    obtain ⟨s, hs⟩ := hSne
    exact le_trans (hMc s (hSK hs)) (hCle s hs)
  -- the neighbourhood
  set N : Set (ℝ × ℝ) := (⋃ i ∈ S, I i) ×ˢ Set.Ioo (-δbar) δbar with hNdef
  have hNopen : IsOpen N := by
    rw [hNdef]
    exact (isOpen_biUnion fun i _ => isOpen_Ioo).prod isOpen_Ioo
  -- the box of one chart, inside `N`
  set B : ℝ → Set (ℝ × ℝ) := fun i => I i ×ˢ Set.Ioo (-δbar) δbar with hBdef
  have hBopen : ∀ i, IsOpen (B i) := fun i => isOpen_Ioo.prod isOpen_Ioo
  have hBsubN : ∀ i ∈ S, B i ⊆ N := by
    intro i hi p hp
    exact ⟨Set.mem_biUnion hi hp.1, hp.2⟩
  -- charts are analytic on their box
  have hBanalytic : ∀ i ∈ S, ∀ p ∈ B i, AnalyticAt ℝ (Gc i) p := by
    intro i hi p hp
    have h1 : |p.1 - i| < w i := (hmem i p.1).mp hp.1
    have h2 : |p.2| ≤ ρ i := by
      have hp2 := hp.2
      rw [Set.mem_Ioo] at hp2
      have hle := hδle i hi
      rw [abs_le]
      exact ⟨by linarith [hp2.1], by linarith [hp2.2]⟩
    have hres := hA1 i (hSK hi) p.1 p.2 h1 h2
    simpa using hres
  have hBanalytic' : ∀ i ∈ S, ∀ p ∈ B i, AnalyticAt ℝ (dDelta (Gc i)) p := by
    intro i hi p hp
    have h1 : |p.1 - i| < w i := (hmem i p.1).mp hp.1
    have h2 : |p.2| ≤ ρ i := by
      have h := hp.2
      rw [Set.mem_Ioo] at h
      have hle := hδle i hi
      rw [abs_le]; constructor <;> linarith
    have hres := hA2 i (hSK hi) p.1 p.2 h1 h2
    simpa using hres
  -- pairwise agreement on the overlap
  have hpair : ∀ i ∈ S, ∀ j ∈ S, ∀ p : ℝ × ℝ, p ∈ B i → p ∈ B j → Gc i p = Gc j p := by
    intro i hi j hj p hpi hpj
    set a : ℝ := max (i - w i) (j - w j) with hadef
    set b : ℝ := min (i + w i) (j + w j) with hbdef
    set D : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ Set.Ioo (-δbar) δbar with hDdef
    have hDsubi : D ⊆ B i := fun z hz =>
      ⟨⟨lt_of_le_of_lt (le_max_left _ _) hz.1.1, lt_of_lt_of_le hz.1.2 (min_le_left _ _)⟩, hz.2⟩
    have hDsubj : D ⊆ B j := fun z hz =>
      ⟨⟨lt_of_le_of_lt (le_max_right _ _) hz.1.1, lt_of_lt_of_le hz.1.2 (min_le_right _ _)⟩, hz.2⟩
    have hpD : p ∈ D := by
      refine ⟨⟨?_, ?_⟩, hpj.2⟩
      · exact max_lt hpi.1.1 hpj.1.1
      · exact lt_min hpi.1.2 hpj.1.2
    -- both charts equal the boundary excess on the upper half box
    set p₀ : ℝ × ℝ := (p.1, δbar / 2) with hp₀def
    have hp₀D : p₀ ∈ D := ⟨hpD.1, by rw [hp₀def]; constructor <;> [linarith; linarith]⟩
    have hupper : Set.Ioo a b ×ˢ Set.Ioo 0 δbar ⊆ {z | Gc i z = Gc j z} := by
      intro z hz
      have hzD : z ∈ D := ⟨hz.1, ⟨by linarith [hz.2.1], hz.2.2⟩⟩
      have h1 := hAgree i (hSK hi) z.1 z.2 ((hmem i z.1).mp (hDsubi hzD).1) hz.2.1
        (lt_of_lt_of_le hz.2.2 (hδle i hi))
      have h2 := hAgree j (hSK hj) z.1 z.2 ((hmem j z.1).mp (hDsubj hzD).1) hz.2.1
        (lt_of_lt_of_le hz.2.2 (hδle j hj))
      show Gc i z = Gc j z
      rw [← h1, ← h2]
    have hev : Gc i =ᶠ[𝓝 p₀] Gc j := by
      have hopen : IsOpen (Set.Ioo a b ×ˢ Set.Ioo (0:ℝ) δbar) := isOpen_Ioo.prod isOpen_Ioo
      have hp₀mem : p₀ ∈ Set.Ioo a b ×ˢ Set.Ioo (0:ℝ) δbar :=
        ⟨hpD.1, by rw [hp₀def]; constructor <;> [linarith; linarith]⟩
      filter_upwards [hopen.mem_nhds hp₀mem] with z hz using hupper hz
    have := eqOn_prod_Ioo_of_eventuallyEq
      (fun z hz => hBanalytic i hi z (hDsubi hz))
      (fun z hz => hBanalytic j hj z (hDsubj hz)) hp₀D hev
    exact this hpD
  -- the glued function
  set pick : ℝ → ℝ := fun r =>
    if h : ∃ i, i ∈ S ∧ r ∈ I i then h.choose else r₁ with hpickdef
  have hpick : ∀ r : ℝ, (∃ i, i ∈ S ∧ r ∈ I i) → pick r ∈ S ∧ r ∈ I (pick r) := by
    intro r h
    rw [hpickdef]
    simp only [dif_pos h]
    exact h.choose_spec
  set G : ℝ × ℝ → ℝ := fun z => Gc (pick z.1) z with hGdef
  have hGeq : ∀ i ∈ S, ∀ p ∈ B i, G p = Gc i p := by
    intro i hi p hp
    have hex : ∃ j, j ∈ S ∧ p.1 ∈ I j := ⟨i, hi, hp.1⟩
    obtain ⟨hjS, hjI⟩ := hpick p.1 hex
    have hpj : p ∈ B (pick p.1) := ⟨hjI, hp.2⟩
    rw [hGdef]
    exact hpair _ hjS i hi p hpj hp
  -- `G` agrees with a chart on a whole neighbourhood, so it inherits analyticity
  have hGloc : ∀ i ∈ S, ∀ p ∈ B i, G =ᶠ[𝓝 p] Gc i := by
    intro i hi p hp
    filter_upwards [(hBopen i).mem_nhds hp] with z hz using hGeq i hi z hz
  have hGana : ∀ p ∈ N, AnalyticAt ℝ G p := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp hp.1
    exact (hBanalytic i hi p ⟨hpi, hp.2⟩).congr (hGloc i hi p ⟨hpi, hp.2⟩).symm
  -- the same for the `δ`-derivative
  have hdGeq : ∀ i ∈ S, ∀ p ∈ B i, dDelta G p = dDelta (Gc i) p := by
    intro i hi p hp
    have hfd : fderiv ℝ G p = fderiv ℝ (Gc i) p := (hGloc i hi p hp).fderiv_eq
    rw [dDelta, dDelta, hfd]
  have hdGloc : ∀ i ∈ S, ∀ p ∈ B i, dDelta G =ᶠ[𝓝 p] dDelta (Gc i) := by
    intro i hi p hp
    filter_upwards [(hBopen i).mem_nhds hp] with z hz using hdGeq i hi z hz
  have hdGana : ∀ p ∈ N, AnalyticAt ℝ (dDelta G) p := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp hp.1
    exact (hBanalytic' i hi p ⟨hpi, hp.2⟩).congr (hdGloc i hi p ⟨hpi, hp.2⟩).symm
  have hd2Geq : ∀ i ∈ S, ∀ p ∈ B i, dDelta (dDelta G) p = dDelta (dDelta (Gc i)) p := by
    intro i hi p hp
    have hfd : fderiv ℝ (dDelta G) p = fderiv ℝ (dDelta (Gc i)) p :=
      (hdGloc i hi p hp).fderiv_eq
    rw [dDelta, dDelta, hfd]
  -- every `r ∈ K` lies in some chart window
  have hKpick : ∀ r ∈ K, ∃ i, i ∈ S ∧ r ∈ I i := by
    intro r hr
    obtain ⟨i, hi, hri⟩ := Set.mem_iUnion₂.mp (hScov hr)
    exact ⟨i, hi, hri⟩
  refine ⟨δbar, C₂, N, G, hδpos, hC0, hNopen, ?_, hGana, hdGana, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr δ hδ
    obtain ⟨i, hi, hri⟩ := hKpick r hr
    exact ⟨Set.mem_biUnion hi hri, by rw [Set.mem_Ioo]; exact abs_lt.mp hδ⟩
  · intro r hr δ hδ0 hδb
    obtain ⟨i, hi, hri⟩ := hKpick r hr
    have hpB : ((r, δ) : ℝ × ℝ) ∈ B i := ⟨hri, ⟨by linarith, hδb⟩⟩
    rw [hGeq i hi _ hpB]
    exact (hAgree i (hSK hi) r δ ((hmem i r).mp hri) hδ0 (lt_of_lt_of_le hδb (hδle i hi))).symm
  · intro r hr
    obtain ⟨i, hi, hri⟩ := hKpick r hr
    have hpB : ((r, (0:ℝ)) : ℝ × ℝ) ∈ B i := ⟨hri, ⟨by linarith, hδpos⟩⟩
    rw [hGeq i hi _ hpB]
    exact hZ0 i (hSK hi) r ((hmem i r).mp hri)
  · intro r hr
    obtain ⟨i, hi, hri⟩ := hKpick r hr
    have hpB : ((r, (0:ℝ)) : ℝ × ℝ) ∈ B i := ⟨hri, ⟨by linarith, hδpos⟩⟩
    rw [hdGeq i hi _ hpB]
    exact hZ1 i (hSK hi) r ((hmem i r).mp hri)
  · intro r hr
    obtain ⟨i, hi, hri⟩ := hKpick r hr
    have hpB : ((r, (0:ℝ)) : ℝ × ℝ) ∈ B i := ⟨hri, ⟨by linarith, hδpos⟩⟩
    rw [hd2Geq i hi _ hpB]
    exact hZ2 i (hSK hi) r ((hmem i r).mp hri)
  · intro r hr δ hδ
    obtain ⟨i, hi, hri⟩ := hKpick r hr
    have hδlt := abs_lt.mp hδ
    have hpB : ((r, δ) : ℝ × ℝ) ∈ B i := ⟨hri, ⟨hδlt.1, hδlt.2⟩⟩
    rw [hd2Geq i hi _ hpB]
    refine le_trans (hCurv i (hSK hi) r δ ((hmem i r).mp hri) ?_)
      (mul_le_mul_of_nonneg_right (hCle i hi) (abs_nonneg δ))
    exact le_trans hδ.le (hδle i hi)


/-- **`thm:positive-second-variation` ("Universal positivity of the scalar second variation").**
For a compact set `K` of non-exceptional densities on a Lubetzky–Zhao boundary arc there are
`δ̄ > 0`, an open neighbourhood `𝒩` of `K × (-δ̄, δ̄)` and a real-analytic `G : 𝒩 → ℝ` with

* `G(r,δ) = G_r(δ)` for `r ∈ K` and `0 < δ < δ̄`  (`eq:boundary-excess-extension`);
* **(i)** `G(r,0) = 0` and `∂_δG(r,0) = 0`;
* **(ii)** `A_H` is real-analytic on `K` and `A_H ≥ a₀ > 0` there;
* **(iii)** `∂²_δG(r,0) = A_H(r)` and `|∂²_δG(r,δ) - A_H(r)| ≤ C₂|δ|` for `|δ| < δ̄`,
  with `C₂ ≥ 1` depending only on `H` and `K`  (`eq:boundary-excess-curvature`);
* **(iv)** `|G_r(δ) - ½A_H(r)δ²| ≤ C_3δ³`  (`eq:boundary-excess-expansion`).

The extension is `boundaryExcess_extension`; clauses (ii) and (iv) are `boundaryExcess_taylor`.
Where the paper *defines* `A_H(r) := ∂²_δG(r,0)`, `AH` is here the chart-independent right limit
`lim_{δ↓0} 2G_r(δ)/δ²` and the displayed equality is part of the conclusion.

The paper states the theorem on an open interval `I ∋ r₀` with compact closure in
`(0,1) ∖ {r_*}`, after shrinking `I`; taking `K` to be that closure gives its form, which is
`positive_second_variation_interval` (`NonexceptionalEndpoint/QuadraticGrowth/Global.lean`). -/
theorem positive_second_variation {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKex : ∀ r ∈ K, r ≠ rStar d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ (δbar a₀ C₂ Ccub : ℝ) (N : Set (ℝ × ℝ)) (G : ℝ × ℝ → ℝ),
      0 < δbar ∧ 0 < a₀ ∧ 1 ≤ C₂ ∧ 0 ≤ Ccub ∧ IsOpen N ∧
      (∀ r ∈ K, ∀ δ : ℝ, |δ| < δbar → (r, δ) ∈ N) ∧
      (∀ p ∈ N, AnalyticAt ℝ G p) ∧
      (∀ r ∈ K, ∀ δ : ℝ, 0 < δ → δ < δbar → G (r, δ) = boundaryExcess H M r δ) ∧
      (∀ r ∈ K, G (r, 0) = 0 ∧ dDelta G (r, 0) = 0) ∧
      (∀ r ∈ K, AnalyticAt ℝ (AH H M) r ∧ a₀ ≤ AH H M r) ∧
      (∀ r ∈ K, dDelta (dDelta G) (r, 0) = AH H M r) ∧
      (∀ r ∈ K, ∀ δ : ℝ, |δ| < δbar →
        |dDelta (dDelta G) (r, δ) - AH H M r| ≤ C₂ * |δ|) ∧
      (∀ r ∈ K, ∀ δ : ℝ, 0 < δ → δ < δbar →
        |boundaryExcess H M r δ - AH H M r * δ ^ 2 / 2| ≤ Ccub * δ ^ 3) := by
  obtain ⟨δ₁, C₂, N, G, hδ₁, hC₂, hNopen, hNmem, hGana, -, hGagree, hG0, hdG0, hd2G0, hcurv⟩ :=
    boundaryExcess_extension hd M hK hKc hKne hKex H hreg hm
  obtain ⟨CA, Ccub, δ₀, hCA, hCcub, hδ₀, hAana, hAlb, hcubic⟩ :=
    boundaryExcess_taylor hd M hK hKc hKne hKex H hreg hm
  refine ⟨min δ₁ δ₀, CA, max C₂ 1, Ccub, N, G, lt_min hδ₁ hδ₀, hCA, le_max_right _ _, hCcub,
    hNopen,
    fun r hr δ hδ => hNmem r hr δ (lt_of_lt_of_le hδ (min_le_left _ _)),
    hGana,
    fun r hr δ hδ0 hδb => hGagree r hr δ hδ0 (lt_of_lt_of_le hδb (min_le_left _ _)),
    fun r hr => ⟨hG0 r hr, hdG0 r hr⟩,
    fun r hr => ⟨hAana r hr, hAlb r hr⟩,
    hd2G0,
    fun r hr δ hδ => le_trans (hcurv r hr δ (lt_of_lt_of_le hδ (min_le_left _ _)))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg δ)),
    fun r hr δ hδ0 hδb => hcubic r hr δ hδ0 (lt_of_lt_of_le hδb (min_le_right _ _))⟩

end UpperTailOptimizers
