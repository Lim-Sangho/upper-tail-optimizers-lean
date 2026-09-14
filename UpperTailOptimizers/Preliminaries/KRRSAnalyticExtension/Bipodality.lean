import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Extension
import UpperTailOptimizers.Preliminaries.Graphons.BipodalIdentifiability

/-!
# `thm:krrs-bipodality` in the paper's form

`thm:krrs-bipodality` (`paper/sections/appendix_preliminaries.tex`, KRR–S Theorem 1.1 for
`d`-regular `H`) is stated with a pointwise threshold `τ₀(ε) > ε^m` and *global* parameter maps
`(ε,τ) ↦ (c, q₁₁, q₁₂, q₂₂)`, jointly real-analytic on
`{(ε,τ) : ε ≠ (d-1)/d, ε^m < τ < τ₀(ε)}`.  `krrs_analytic_extension` (`Preliminaries/KRRSAnalyticExtension/Extension.lean`)
supplies the same conclusions on local charts `U × (0,Δ)` in the coordinates `(ε, ϑ = τ - ε^m)`.
`krrs_bipodality` glues these charts into the global statement:

* for `ε ∈ (0,1) ∖ {r_*}` and `ε^m < τ < τ₀(ε)`, the entropy maximizer at `(e,t_H) = (ε,τ)`
  exists, is unique up to relabelling and bipodal, and is a.e. the two-block graphon with
  smaller block `[0, c(ε,τ)]`, `0 < c(ε,τ) < 1/2`, and levels `q₁₁, q₁₂, q₂₂ ∈ (0,1)`;
* `c, q₁₁, q₁₂, q₂₂` are real-analytic, as functions on `ℝ²`, at every point of the region;
* for each fixed nonexceptional `ε`, as `τ ↓ ε^m`: `q₁₁ → a_d(ε) ∈ (0,1)`,
  `q₁₂ → ζ_d(ε) ≠ ε`, `q₂₂ → ε`, and `|c(ε,τ)| ≤ K_ε (τ - ε^m)` on all of `(ε^m, τ₀(ε))`;
* in addition, the region is open and `τ₀` is locally uniform: near every nonexceptional `ε₀`
  it stays above `ε^m + Δ` for a fixed `Δ > 0` (the consequences of joint analyticity noted
  after the theorem and in `sec:preliminaries`).

## Proof

*The parameters.*  `krrsParamSet H ε τ` is the set of tuples `(c, q₁₁, q₁₂, q₂₂)` with
`c ∈ (0,1/2)` realised by an entropy maximizer at `(ε,τ)`, and `krrsParams H ε τ` is a choice
from it.  If the maximizer is unique up to relabelling and `τ ≠ ε^m`, the set is a singleton
(`krrsParams_eq_of_unique`): two tuples give two maximizers, hence a relabelling between their
two-block graphons, and `bipodal_params_eq_of_relabel` (`Preliminaries/Graphons/BipodalIdentifiability.lean`)
identifies the tuples; nonconstancy of the levels holds because a constant graphon has
`t_H = e^m ≠ τ`.  So every chart of `krrs_analytic_extension` computes `krrsParams` on its
domain.

*The threshold.*  `τ₀(ε) = ε^m + sup {min(1, Δ(ε₀)) : ε ∈ U(ε₀)}` over the charts
`(U(ε₀), Δ(ε₀))` chosen at the nonexceptional `ε₀`.  Every `(ε,τ)` in the region then lies in
a chart domain `{ε ∈ U(ε₀), 0 < τ - ε^m < min(1, Δ(ε₀))}`, which is open and contained in the
region; on it the global parameters are the chart's analytic functions composed with
`(ε,τ) ↦ (ε, τ - ε^m)`, which gives analyticity and openness.
The limits and the bound on `c` come from the chart at `ε₀ = ε` and its base values; beyond
that chart's height `Δ(ε)` the bound on `c` follows from `c < 1/2`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The parameters of the maximizer -/

/-- The tuples `(c, q₁₁, q₁₂, q₂₂)`, `c ∈ (0,1/2)`, such that some entropy maximizer at
`(e, t_H) = (ε, τ)` is a.e. the two-block graphon with first block `[0,c]` and levels
`q₁₁, q₁₂, q₂₂`. -/
def krrsParamSet (H : SimpleGraph V) [DecidableRel H.Adj] (ε τ : ℝ) :
    Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ioo (0:ℝ) (1 / 2) ∧
    ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
      (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy ≤ W.entropy) ∧
      ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue (Set.Icc 0 p.1) p.2.1 p.2.2.1 p.2.2.2 z}

/-- **The bipodal parameters `(c, q₁₁, q₁₂, q₂₂)` of the entropy maximizer at `(ε, τ)`**: a
choice from `krrsParamSet H ε τ`, which is a singleton whenever the maximizer is unique up to
relabelling and `τ ≠ ε^m` (`krrsParams_eq_of_unique`). -/
noncomputable def krrsParams (H : SimpleGraph V) [DecidableRel H.Adj] (ε τ : ℝ) :
    ℝ × ℝ × ℝ × ℝ :=
  Classical.epsilon (· ∈ krrsParamSet H ε τ)

/-- A two-block graphon with `t(H,W) ≠ e(W)^m` does not have three equal levels: otherwise it
is a.e. constant, and then `t(H,W) = e(W)^m`. -/
theorem bipodal_levels_not_const {H : SimpleGraph V} [DecidableRel H.Adj] {W : Graphon}
    {A : Set ℝ} {q11 q12 q22 : ℝ}
    (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue A q11 q12 q22 z)
    (ht : W.tDensity H ≠ W.edgeDensity ^ H.edgeFinset.card) : ¬(q11 = q12 ∧ q12 = q22) := by
  rintro ⟨h1, h2⟩
  have hc : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = q11 := by
    filter_upwards [hW] with z hz
    rw [hz, ← h2, ← h1]
    unfold bipodalValue
    split_ifs <;> rfl
  exact ht (by rw [tDensity_ae_const W H hc, edgeDensity_ae_const W hc])

/-- **The maximizer's parameters are well defined.**  If `W` is an entropy maximizer at
`(ε, τ)`, `τ ≠ ε^m`, that is unique up to relabelling and a.e. the two-block graphon with
parameters `p = (c, q₁₁, q₁₂, q₂₂)`, `c ∈ (0,1/2)`, then `krrsParams H ε τ = p`. -/
theorem krrsParams_eq_of_unique (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ}
    (hτ : τ ≠ ε ^ H.edgeFinset.card) {W : Graphon} {p : ℝ × ℝ × ℝ × ℝ}
    (hp : p.1 ∈ Set.Ioo (0:ℝ) (1 / 2)) (he : W.edgeDensity = ε) (ht : W.tDensity H = τ)
    (hmax : ∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy ≤ W.entropy)
    (huniq : ∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
      W'.entropy = W.entropy →
      ∃ σ : ℝ → ℝ, IsRelabelling σ ∧ ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2))
    (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue (Set.Icc 0 p.1) p.2.1 p.2.2.1 p.2.2.2 z) :
    krrsParams H ε τ = p := by
  have hmem : p ∈ krrsParamSet H ε τ := ⟨hp, W, he, ht, hmax, hW⟩
  obtain ⟨hc', W', he', ht', hmax', hW'⟩ : krrsParams H ε τ ∈ krrsParamSet H ε τ :=
    Classical.epsilon_spec ⟨p, hmem⟩
  have hent : W'.entropy = W.entropy := le_antisymm (hmax W' he' ht') (hmax' W he ht)
  obtain ⟨σ, hσ, hrel⟩ := huniq W' he' ht' hent
  have hq := bipodal_levels_not_const (H := H) hW (by rw [he, ht]; exact hτ)
  have hq' := bipodal_levels_not_const (H := H) hW' (by rw [he', ht']; exact hτ)
  obtain ⟨h1, h2, h3, h4⟩ := bipodal_params_eq_of_relabel hσ hp hc' hq hq' hW hW' hrel
  exact Prod.ext h1.symm (Prod.ext h2.symm (Prod.ext h3.symm h4.symm))

/-! ### The theorem -/

/-- **`thm:krrs-bipodality`** (KRR–S bipodality for regular graphs, KRR–S Theorem 1.1).  Let
`H` be `d`-regular, `d ≥ 2`, with `m ≥ 2` edges.  There are a threshold `τ₀(ε) > ε^m` and
parameter maps `c, q₁₁, q₁₂, q₂₂` of `(ε, τ)` such that, for `ε ∈ (0,1) ∖ {(d-1)/d}` and
`ε^m < τ < τ₀(ε)`, the entropy maximizer subject to `e(W) = ε`, `t(H,W) = τ` is unique up to
relabelling and bipodal, with smaller block `[0,c]` of size `c` and edge probabilities `q₁₁`
within it, `q₁₂` between the blocks and `q₂₂` within the larger block; these parameters are
jointly real-analytic in `(ε,τ)` on the region `{ε ≠ (d-1)/d, ε^m < τ < τ₀(ε)}`; and for each
fixed nonexceptional `ε`, as `τ ↓ ε^m`, `q₁₁ → a_d(ε) ∈ (0,1)`, `q₁₂ → ζ_d(ε) ≠ ε`,
`q₂₂ → ε` and `c = O_{H,ε}(τ - ε^m)`.

The last two clauses add what the paper derives from joint analyticity right after the theorem
and in `sec:preliminaries`: the region is open, and near every nonexceptional `ε₀` a single
`Δ > 0` has `τ₀(ε) ≥ ε^m + Δ`. -/
theorem krrs_bipodality (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card) :
    ∃ (τ₀ : ℝ → ℝ) (c q11 q12 q22 : ℝ → ℝ → ℝ) (ad : ℝ → ℝ),
      -- the threshold `τ₀(ε) > ε^m`
      (∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d → ε ^ H.edgeFinset.card < τ₀ ε) ∧
      -- the entropy maximizer for `ε^m < τ < τ₀(ε)`: unique up to relabelling, bipodal, with
      -- smaller block `[0, c(ε,τ)]` and levels `q₁₁, q₁₂, q₂₂`
      (∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d → ∀ τ : ℝ, ε ^ H.edgeFinset.card < τ → τ < τ₀ ε →
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy ≤ W.entropy) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy = W.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) ∧
          IsBipodal W ∧
          c ε τ ∈ Set.Ioo (0:ℝ) (1 / 2) ∧ q11 ε τ ∈ Set.Ioo (0:ℝ) 1 ∧
          q12 ε τ ∈ Set.Ioo (0:ℝ) 1 ∧ q22 ε τ ∈ Set.Ioo (0:ℝ) 1 ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2
            = bipodalValue (Set.Icc 0 (c ε τ)) (q11 ε τ) (q12 ε τ) (q22 ε τ) z)) ∧
      -- joint real-analyticity on `{(ε,τ) : ε ≠ (d-1)/d, ε^m < τ < τ₀(ε)}`
      (∀ ε τ : ℝ, ε ∈ Set.Ioo (0:ℝ) 1 → ε ≠ rStar d → ε ^ H.edgeFinset.card < τ →
        τ < τ₀ ε →
        AnalyticAt ℝ (fun p : ℝ × ℝ => c p.1 p.2) (ε, τ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (ε, τ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (ε, τ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (ε, τ)) ∧
      -- the limits as `τ ↓ ε^m`, for each fixed nonexceptional `ε`
      (∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d →
        ad ε ∈ Set.Ioo (0:ℝ) 1 ∧ zetaFun d ε ≠ ε ∧
        Tendsto (fun τ => q11 ε τ) (𝓝[>] (ε ^ H.edgeFinset.card)) (𝓝 (ad ε)) ∧
        Tendsto (fun τ => q12 ε τ) (𝓝[>] (ε ^ H.edgeFinset.card)) (𝓝 (zetaFun d ε)) ∧
        Tendsto (fun τ => q22 ε τ) (𝓝[>] (ε ^ H.edgeFinset.card)) (𝓝 ε) ∧
        ∃ K : ℝ, ∀ τ : ℝ, ε ^ H.edgeFinset.card < τ → τ < τ₀ ε →
          |c ε τ| ≤ K * (τ - ε ^ H.edgeFinset.card)) ∧
      -- the region is open, and `τ₀` is locally uniform
      IsOpen {p : ℝ × ℝ | p.1 ∈ Set.Ioo (0:ℝ) 1 ∧ p.1 ≠ rStar d ∧
        p.1 ^ H.edgeFinset.card < p.2 ∧ p.2 < τ₀ p.1} ∧
      (∀ ε₀ ∈ Set.Ioo (0:ℝ) 1, ε₀ ≠ rStar d →
        ∃ (U : Set ℝ) (Δ : ℝ), IsOpen U ∧ ε₀ ∈ U ∧ U ⊆ Set.Ioo (0:ℝ) 1 \ {rStar d} ∧
          0 < Δ ∧ ∀ ε ∈ U, ε ^ H.edgeFinset.card + Δ ≤ τ₀ ε) := by
  -- a chart of `krrs_analytic_extension` at every nonexceptional base point
  have hext := fun (ε₀ : ℝ) (h : ε₀ ∈ Set.Ioo (0:ℝ) 1 ∧ ε₀ ≠ rStar d) =>
    krrs_analytic_extension H hd hreg hm h.1.1 h.1.2 h.2
  choose! U Δ Q11 Q12 Q22 C hch using hext
  set m := H.edgeFinset.card with hmdef
  -- the chart heights available at `ε`, and their supremum
  obtain ⟨Ds, hDs⟩ : ∃ Ds : ℝ → ℝ, Ds = fun ε => sSup {δ : ℝ | ∃ ε₀ : ℝ,
      (ε₀ ∈ Set.Ioo (0:ℝ) 1 ∧ ε₀ ≠ rStar d) ∧ ε ∈ U ε₀ ∧ δ = min 1 (Δ ε₀)} := ⟨_, rfl⟩
  have hDs_ge : ∀ ε ε₀ : ℝ, ε₀ ∈ Set.Ioo (0:ℝ) 1 → ε₀ ≠ rStar d → ε ∈ U ε₀ →
      min 1 (Δ ε₀) ≤ Ds ε := by
    intro ε ε₀ h1 h2 hε
    rw [hDs]
    exact le_csSup ⟨1, by rintro δ ⟨ε₁, -, -, rfl⟩; exact min_le_left _ _⟩
      ⟨ε₀, ⟨h1, h2⟩, hε, rfl⟩
  have hDs_lt : ∀ ε x : ℝ, ε ∈ Set.Ioo (0:ℝ) 1 → ε ≠ rStar d → x < Ds ε →
      ∃ ε₀ : ℝ, (ε₀ ∈ Set.Ioo (0:ℝ) 1 ∧ ε₀ ≠ rStar d) ∧ ε ∈ U ε₀ ∧ x < min 1 (Δ ε₀) := by
    intro ε x h1 h2 hx
    simp only [hDs] at hx
    have hne : {δ : ℝ | ∃ ε₀ : ℝ, (ε₀ ∈ Set.Ioo (0:ℝ) 1 ∧ ε₀ ≠ rStar d) ∧ ε ∈ U ε₀ ∧
        δ = min 1 (Δ ε₀)}.Nonempty :=
      ⟨min 1 (Δ ε), ε, ⟨h1, h2⟩, (hch ε ⟨h1, h2⟩).2.1, rfl⟩
    obtain ⟨δ, ⟨ε₀, hε₀, hε, rfl⟩, hxδ⟩ := exists_lt_of_lt_csSup hne hx
    exact ⟨ε₀, hε₀, hε, hxδ⟩
  have hDs_pos : ∀ ε : ℝ, ε ∈ Set.Ioo (0:ℝ) 1 → ε ≠ rStar d → 0 < Ds ε := fun ε h1 h2 =>
    lt_of_lt_of_le (lt_min one_pos (hch ε ⟨h1, h2⟩).2.2.2.1)
      (hDs_ge ε ε h1 h2 (hch ε ⟨h1, h2⟩).2.1)
  -- every chart computes the global parameters on its domain
  have hagree : ∀ ε₀ : ℝ, ε₀ ∈ Set.Ioo (0:ℝ) 1 → ε₀ ≠ rStar d → ∀ ε ∈ U ε₀, ∀ τ : ℝ,
      0 < τ - ε ^ m → τ - ε ^ m < Δ ε₀ →
      krrsParams H ε τ = (C ε₀ ε (τ - ε ^ m), Q11 ε₀ ε (τ - ε ^ m), Q12 ε₀ ε (τ - ε ^ m),
        Q22 ε₀ ε (τ - ε ^ m)) := by
    intro ε₀ h1 h2 ε hε τ hs0 hsΔ
    obtain ⟨W, he, ht, hmx, huq, -, hc, -, -, -, hW⟩ :=
      (hch ε₀ ⟨h1, h2⟩).2.2.2.2.1 ε hε τ hs0 hsΔ
    exact krrsParams_eq_of_unique H (sub_pos.mp hs0).ne' hc he ht hmx huq hW
  -- every point of the region lies in a chart domain
  have hcover : ∀ ε τ : ℝ, ε ∈ Set.Ioo (0:ℝ) 1 → ε ≠ rStar d → τ < ε ^ m + Ds ε →
      ∃ ε₀ : ℝ, (ε₀ ∈ Set.Ioo (0:ℝ) 1 ∧ ε₀ ≠ rStar d) ∧ ε ∈ U ε₀ ∧ τ - ε ^ m < Δ ε₀ :=
    fun ε τ h1 h2 hτ => by
      obtain ⟨ε₀, hε₀, hε, hlt⟩ := hDs_lt ε (τ - ε ^ m) h1 h2 (by linarith)
      exact ⟨ε₀, hε₀, hε, lt_of_lt_of_le hlt (min_le_right _ _)⟩
  -- the maximizer clause
  have hmaxcl : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d → ∀ τ : ℝ, ε ^ m < τ →
      τ < ε ^ m + Ds ε →
      ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
        (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
          W'.entropy ≤ W.entropy) ∧
        (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
          W'.entropy = W.entropy →
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) ∧
        IsBipodal W ∧
        (krrsParams H ε τ).1 ∈ Set.Ioo (0:ℝ) (1 / 2) ∧
        (krrsParams H ε τ).2.1 ∈ Set.Ioo (0:ℝ) 1 ∧
        (krrsParams H ε τ).2.2.1 ∈ Set.Ioo (0:ℝ) 1 ∧
        (krrsParams H ε τ).2.2.2 ∈ Set.Ioo (0:ℝ) 1 ∧
        (∀ᵐ z ∂gμ, W.toFun z.1 z.2
          = bipodalValue (Set.Icc 0 (krrsParams H ε τ).1) (krrsParams H ε τ).2.1
              (krrsParams H ε τ).2.2.1 (krrsParams H ε τ).2.2.2 z) := by
    intro ε h1 h2 τ hτ1 hτ2
    obtain ⟨ε₀, ⟨h01, h02⟩, hε, hsΔ⟩ := hcover ε τ h1 h2 hτ2
    have hs0 : 0 < τ - ε ^ m := sub_pos.mpr hτ1
    obtain ⟨W, he, ht, hmx, huq, hbip, hc, hq11, hq12, hq22, hW⟩ :=
      (hch ε₀ ⟨h01, h02⟩).2.2.2.2.1 ε hε τ hs0 hsΔ
    rw [hagree ε₀ h01 h02 ε hε τ hs0 hsΔ]
    exact ⟨W, he, ht, hmx, huq, hbip, hc, hq11, hq12, hq22, hW⟩
  refine ⟨fun ε => ε ^ m + Ds ε, fun ε τ => (krrsParams H ε τ).1,
    fun ε τ => (krrsParams H ε τ).2.1, fun ε τ => (krrsParams H ε τ).2.2.1,
    fun ε τ => (krrsParams H ε τ).2.2.2, fun ε => Q11 ε ε 0,
    fun ε h1 h2 => by linarith [hDs_pos ε h1 h2], hmaxcl, ?_, ?_, ?_, ?_⟩
  · -- joint analyticity
    intro ε τ h1 h2 hτ1 hτ2
    obtain ⟨ε₀, ⟨h01, h02⟩, hε, hsΔ⟩ := hcover ε τ h1 h2 hτ2
    obtain ⟨hUo, -, -, -, -, hA11, hA12, hA22, hAc, -⟩ := hch ε₀ ⟨h01, h02⟩
    have hs0 : 0 < τ - ε ^ m := sub_pos.mpr hτ1
    -- the open chart domain in `(ε,τ)` coordinates
    set O : Set (ℝ × ℝ) := {p | p.1 ∈ U ε₀ ∧ 0 < p.2 - p.1 ^ m ∧ p.2 - p.1 ^ m < Δ ε₀}
      with hOdef
    have hOopen : IsOpen O := by
      have hcont : Continuous fun p : ℝ × ℝ => p.2 - p.1 ^ m :=
        continuous_snd.sub (continuous_fst.pow _)
      exact (hUo.preimage continuous_fst).inter
        ((isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const))
    have hOmem : O ∈ 𝓝 (ε, τ) := hOopen.mem_nhds ⟨hε, hs0, hsΔ⟩
    have hPO : ∀ p ∈ O, krrsParams H p.1 p.2 = (C ε₀ p.1 (p.2 - p.1 ^ m),
        Q11 ε₀ p.1 (p.2 - p.1 ^ m), Q12 ε₀ p.1 (p.2 - p.1 ^ m), Q22 ε₀ p.1 (p.2 - p.1 ^ m)) :=
      fun p hp => hagree ε₀ h01 h02 p.1 hp.1 p.2 hp.2.1 hp.2.2
    -- the shift `(ε,τ) ↦ (ε, τ - ε^m)`
    have hg : AnalyticAt ℝ (fun p : ℝ × ℝ => ((p.1, p.2 - p.1 ^ m) : ℝ × ℝ)) (ε, τ) :=
      analyticAt_fst.prod (analyticAt_snd.sub (analyticAt_fst.pow _))
    have hmemS : ((ε, τ - ε ^ m) : ℝ × ℝ) ∈ U ε₀ ×ˢ Set.Ioo (-Δ ε₀) (Δ ε₀) :=
      ⟨hε, by linarith, hsΔ⟩
    have hlift : ∀ F : ℝ → ℝ → ℝ,
        AnalyticOnNhd ℝ (fun p : ℝ × ℝ => F p.1 p.2) (U ε₀ ×ˢ Set.Ioo (-Δ ε₀) (Δ ε₀)) →
        ∀ G : ℝ → ℝ → ℝ, (∀ p ∈ O, G p.1 p.2 = F p.1 (p.2 - p.1 ^ m)) →
        AnalyticAt ℝ (fun p : ℝ × ℝ => G p.1 p.2) (ε, τ) := by
      intro F hF G hGF
      have hcomp : AnalyticAt ℝ (fun p : ℝ × ℝ => F p.1 (p.2 - p.1 ^ m)) (ε, τ) :=
        (hF _ hmemS).comp_of_eq hg rfl
      refine hcomp.congr ?_
      filter_upwards [hOmem] with p hp
      exact (hGF p hp).symm
    exact ⟨hlift _ hAc (fun ε τ => (krrsParams H ε τ).1) fun p hp => by rw [hPO p hp],
      hlift _ hA11 (fun ε τ => (krrsParams H ε τ).2.1) fun p hp => by rw [hPO p hp],
      hlift _ hA12 (fun ε τ => (krrsParams H ε τ).2.2.1) fun p hp => by rw [hPO p hp],
      hlift _ hA22 (fun ε τ => (krrsParams H ε τ).2.2.2) fun p hp => by rw [hPO p hp]⟩
  · -- the limits as `τ ↓ ε^m`, from the chart at `ε₀ = ε`
    intro ε h1 h2
    obtain ⟨-, hεU, -, hΔ0, -, hA11, hA12, hA22, -, hbase, hbd, -⟩ := hch ε ⟨h1, h2⟩
    obtain ⟨hb11, hb12, -, hb22, -⟩ := hbase ε hεU
    have hmemS : ((ε, 0) : ℝ × ℝ) ∈ U ε ×ˢ Set.Ioo (-Δ ε) (Δ ε) :=
      ⟨hεU, by linarith, hΔ0⟩
    have hshift : Tendsto (fun τ : ℝ => τ - ε ^ m) (𝓝[>] (ε ^ m)) (𝓝 0) := by
      have h : Tendsto (fun τ : ℝ => τ - ε ^ m) (𝓝 (ε ^ m)) (𝓝 (ε ^ m - ε ^ m)) :=
        tendsto_id.sub tendsto_const_nhds
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ τ in 𝓝[>] (ε ^ m), krrsParams H ε τ = (C ε ε (τ - ε ^ m),
        Q11 ε ε (τ - ε ^ m), Q12 ε ε (τ - ε ^ m), Q22 ε ε (τ - ε ^ m)) := by
      filter_upwards [Ioo_mem_nhdsGT (show ε ^ m < ε ^ m + Δ ε by linarith)] with τ hτ
      exact hagree ε h1 h2 ε hεU τ (by linarith [hτ.1]) (by linarith [hτ.2])
    have hlim : ∀ F : ℝ → ℝ → ℝ,
        AnalyticOnNhd ℝ (fun p : ℝ × ℝ => F p.1 p.2) (U ε ×ˢ Set.Ioo (-Δ ε) (Δ ε)) →
        ∀ G : ℝ → ℝ, (∀ᶠ τ in 𝓝[>] (ε ^ m), G τ = F ε (τ - ε ^ m)) →
        Tendsto G (𝓝[>] (ε ^ m)) (𝓝 (F ε 0)) := by
      intro F hF G hGF
      have hcont : ContinuousAt (fun ϑ : ℝ => F ε ϑ) 0 :=
        (hF _ hmemS).continuousAt.comp_of_eq
          (continuousAt_const.prodMk continuousAt_id) rfl
      exact (hcont.tendsto.comp hshift).congr' (hGF.mono fun τ h => h.symm)
    have l11 := hlim _ hA11 (fun τ => (krrsParams H ε τ).2.1) (hev.mono fun τ h => by rw [h])
    have l12 := hlim _ hA12 (fun τ => (krrsParams H ε τ).2.2.1)
      (hev.mono fun τ h => by rw [h])
    have l22 := hlim _ hA22 (fun τ => (krrsParams H ε τ).2.2.2)
      (hev.mono fun τ h => by rw [h])
    rw [hb12] at l12
    rw [hb22] at l22
    refine ⟨hb11, zetaFun_ne_self hd h1 h2, l11, l12, l22, ?_⟩
    -- `c = O(τ - ε^m)`: the chart bound below `Δ(ε)`, and `c < 1/2` above it
    obtain ⟨Cb, hCb0, hCb⟩ := hbd
    refine ⟨Cb + 1 / (2 * Δ ε), fun τ hτ1 hτ2 => ?_⟩
    show |(krrsParams H ε τ).1| ≤ (Cb + 1 / (2 * Δ ε)) * (τ - ε ^ m)
    have hs0 : 0 < τ - ε ^ m := sub_pos.mpr hτ1
    obtain ⟨-, -, -, -, -, -, hc, -⟩ := hmaxcl ε h1 h2 τ hτ1 hτ2
    have hCs : 0 ≤ Cb * (τ - ε ^ m) := mul_nonneg hCb0.le hs0.le
    have hDs' : 0 ≤ 1 / (2 * Δ ε) * (τ - ε ^ m) := by positivity
    have hsplit : (Cb + 1 / (2 * Δ ε)) * (τ - ε ^ m)
        = Cb * (τ - ε ^ m) + 1 / (2 * Δ ε) * (τ - ε ^ m) := by ring
    rw [hsplit]
    by_cases hsm : τ - ε ^ m < Δ ε
    · have hb := hCb ε hεU (τ - ε ^ m) hs0 hsm
      rw [hagree ε h1 h2 ε hεU τ hs0 hsm]
      linarith
    · push Not at hsm
      have hhalf : 1 / 2 ≤ 1 / (2 * Δ ε) * (τ - ε ^ m) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
        linarith
      rw [abs_of_pos hc.1]
      linarith [hc.2]
  · -- the region is open: it contains a chart domain around each of its points
    refine isOpen_iff_mem_nhds.mpr fun p hp => ?_
    obtain ⟨h1, h2, hτ1, hτ2⟩ := hp
    obtain ⟨ε₀, ⟨h01, h02⟩, hε, hlt⟩ := hDs_lt p.1 (p.2 - p.1 ^ m) h1 h2 (by
      change p.2 < p.1 ^ m + Ds p.1 at hτ2; linarith)
    obtain ⟨hUo, -, hUsub, -⟩ := hch ε₀ ⟨h01, h02⟩
    have hcont : Continuous fun q : ℝ × ℝ => q.2 - q.1 ^ m :=
      continuous_snd.sub (continuous_fst.pow _)
    have hOopen : IsOpen {q : ℝ × ℝ | q.1 ∈ U ε₀ ∧ 0 < q.2 - q.1 ^ m ∧
        q.2 - q.1 ^ m < min 1 (Δ ε₀)} :=
      (hUo.preimage continuous_fst).inter
        ((isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const))
    have hs0 : 0 < p.2 - p.1 ^ m := sub_pos.mpr hτ1
    filter_upwards [hOopen.mem_nhds ⟨hε, hs0, hlt⟩] with q hq
    obtain ⟨hqU, hq0, hqlt⟩ := hq
    have hqN := hUsub hqU
    refine ⟨hqN.1, hqN.2, sub_pos.mp hq0, ?_⟩
    linarith [hDs_ge q.1 ε₀ h01 h02 hqU]
  · -- the local uniformity of `τ₀`
    intro ε₀ h1 h2
    obtain ⟨hUo, hmem, hsub, hΔ0, -⟩ := hch ε₀ ⟨h1, h2⟩
    refine ⟨U ε₀, min 1 (Δ ε₀), hUo, hmem, hsub, lt_min one_pos hΔ0, fun ε hε => ?_⟩
    show ε ^ m + min 1 (Δ ε₀) ≤ ε ^ m + Ds ε
    linarith [hDs_ge ε ε₀ h1 h2 hε]

end UpperTailOptimizers
