import UpperTailOptimizers.NonexceptionalEndpoint.Proof.ParameterAsymptotics
import UpperTailOptimizers.NonexceptionalEndpoint.Proof.Main
import UpperTailOptimizers.NonexceptionalEndpoint.Proof.CrossDensity
import UpperTailOptimizers.NonexceptionalEndpoint.LocalReduction.Global

/-!
# `rmk:bipodal-parameter-expansions` in the paper's coordinates

`parameter_asymptotics` (`NonexceptionalEndpoint/Proof/ParameterAsymptotics.lean`) proves the expansions of
`rmk:bipodal-parameter-expansions` on a Lubetzky–Zhao boundary arc, with the boundary value
`q₁₂(r,0)` of the KRR–S parameter map in place of `ζ_d(r)`.  This file states the remark in
global boundary coordinates (`pcGlobal`, `lambdaGlobal`, `AHGlobal`), on the neighbourhood
`U = {|r - r₀| < ρ, |p - pc(r)| < η}` of `thm:nonexceptional-endpoint` with `p < pc(r)`, and with
`ζ_d(r)` itself.

* `bipodal_parameter_expansions` — the remark: the relation `δ_* = 2D_d(r,z)c + O(δ_*²)`,
  `eq:optimizer-block-size`, `eq:optimizer-block-density`, and the first-order bounds for
  `q₁₂` and `q₁₁`, where `z = ζ_d(r)` and `δ_* = r - e(W_{p,r})`.  The KRR–S parameter maps are
  functions of `(ε, ϑ) = (e, t_H - e^m)`, evaluated at `(e(W_{p,r}), r^m - e(W_{p,r})^m)`; the
  statement records that near every `(ε, ϑ) = (r, 0)` they are the analytically extended
  parameter maps of `thm:krrs-analytic-extension`, so `q₁₁⁰(r) = q₁₁(r,0)` is the paper's value.
* `bipodal_block_size_two` — the specialization for `d = 2` used in the introduction:
  `c(p,r) = r λ(p,r)/((2r-1)² A_H(r)) + O(λ(p,r)²)`, from `ζ_2(r) = 1 - r`.

The identity `ζ_d(r) = sm(r)` of the remark is `zetaFun_eq_smGlobal`
(`NonexceptionalEndpoint/Proof/CrossDensity.lean`).
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set Filter Topology

/-- **`rmk:bipodal-parameter-expansions` (first-order asymptotics of the bipodal parameters).**
On `U = {|r - r₀| < ρ, pc(r) - η < p < pc(r)}`, the unique optimizer `W_{p,r}` is the bipodal
graphon whose first block `[0, c]` is its smaller block, with the parameters
`(c, q₁₁, q₁₂, q₂₂)` of the KRR–S map at `(ε, ϑ) = (e(W_{p,r}), r^m - e(W_{p,r})^m)`.

The maps `q₁₁, q₁₂, q₂₂, c` are functions of the coordinates `(ε, ϑ)` of
`thm:krrs-analytic-extension`, with `ϑ = τ - ε^m`.  For every `r` with `|r - r₀| < ρ` they are the
analytically extended KRR–S parameter maps near `(ε, ϑ) = (r, 0)`: they are analytic at `(r, ϑ)`
for `|ϑ| < Δ`, their boundary values are `c(r,0) = 0`, `q₂₂(r,0) = r`, `q₁₂(r,0) = ζ_d(r)`,
`q₁₁(r,0) ∈ (0,1)`, and for `0 < ϑ = τ - r^m < Δ` the entropy maximizer `B` at
`(e, t_H) = (r, τ)` is unique up to relabelling, bipodal, and equal a.e. to the two-block graphon
with first block `[0, c(r,ϑ)]`, `0 < c(r,ϑ) < 1/2`, and densities `q₁₁(r,ϑ), q₁₂(r,ϑ), q₂₂(r,ϑ)`.
So `q₁₁⁰(r) := q₁₁(r,0)` is the value at `(r,0)` of the analytically extended KRR–S parameter
`q₁₁`, as in the paper.

With `δ_* = r - e(W_{p,r})`, `z = ζ_d(r)`, `λ = λ(p,r)` and `q₁₁⁰(r) = q₁₁(r,0)`, and one constant `C`
uniform on `U`:

* `D_d(r,z) ≥ κ > 0`;
* `δ_* = 2D_d(r,z)c + O(δ_*²)`;
* `c = λ/(2D_d(r,z)A_H(r)) + O(λ²)`  (`eq:optimizer-block-size`);
* `q₂₂ = r - (z^d - r^d)/(d r^{d-1}D_d(r,z)A_H(r)) λ + O(λ²)`  (`eq:optimizer-block-density`);
* `q₁₂ = z + O(λ)` and `q₁₁ = q₁₁⁰(r) + O(λ)`. -/
theorem bipodal_parameter_expansions {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ x, H.degree x = d)
    (hm : 1 ≤ H.edgeFinset.card) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ rStar d) :
    ∃ ρ η C κ Δ : ℝ, 0 < ρ ∧ 0 < η ∧ 0 ≤ C ∧ 0 < κ ∧ 0 < Δ ∧
      ∃ q11 q12 q22 c : ℝ → ℝ → ℝ,
        (∀ r : ℝ, |r - r₀| < ρ →
          0 < r ∧ r < 1 ∧ r ≠ rStar d ∧
          c r 0 = 0 ∧ q22 r 0 = r ∧ q12 r 0 = zetaFun d r ∧ q11 r 0 ∈ Set.Ioo (0:ℝ) 1 ∧
          κ ≤ Dd d r (zetaFun d r) ∧
          -- `thm:krrs-analytic-extension` near `(ε, ϑ) = (r, 0)`: these are the analytically
          -- extended KRR–S parameter maps, so `q11 r 0` is the paper's `q₁₁⁰(r)`
          (∀ ϑ : ℝ, |ϑ| < Δ →
            AnalyticAt ℝ (fun x : ℝ × ℝ => q11 x.1 x.2) (r, ϑ) ∧
            AnalyticAt ℝ (fun x : ℝ × ℝ => q12 x.1 x.2) (r, ϑ) ∧
            AnalyticAt ℝ (fun x : ℝ × ℝ => q22 x.1 x.2) (r, ϑ) ∧
            AnalyticAt ℝ (fun x : ℝ × ℝ => c x.1 x.2) (r, ϑ)) ∧
          (∀ τ : ℝ, 0 < τ - r ^ H.edgeFinset.card → τ - r ^ H.edgeFinset.card < Δ →
            ∃ B : Graphon, B.edgeDensity = r ∧ B.tDensity H = τ ∧
              (∀ W' : Graphon, W'.edgeDensity = r → W'.tDensity H = τ →
                W'.entropy ≤ B.entropy) ∧
              (∀ W' : Graphon, W'.edgeDensity = r → W'.tDensity H = τ →
                W'.entropy = B.entropy →
                ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                  ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = B.toFun (σ z.1) (σ z.2)) ∧
              IsBipodal B ∧
              c r (τ - r ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) (1 / 2) ∧
              (∀ᵐ z ∂gμ, B.toFun z.1 z.2
                = bipodalValue (Set.Icc 0 (c r (τ - r ^ H.edgeFinset.card)))
                    (q11 r (τ - r ^ H.edgeFinset.card))
                    (q12 r (τ - r ^ H.edgeFinset.card))
                    (q22 r (τ - r ^ H.edgeFinset.card)) z))) ∧
        ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, pcGlobal d r - η < p → p < pcGlobal d r →
          ∃ W : Graphon, Feasible H r W ∧ W.Ip p = phiVar H p r ∧
            (∀ W' : Graphon, Feasible H r W' → W'.Ip p = phiVar H p r →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) ∧
            (∀ᵐ z ∂gμ, W.toFun z.1 z.2
              = bipodalValue
                  (Set.Icc 0 (c W.edgeDensity (r ^ H.edgeFinset.card
                    - W.edgeDensity ^ H.edgeFinset.card)))
                  (q11 W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card))
                  (q12 W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card))
                  (q22 W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card))
                  z) ∧
            c W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card)
              ∈ Set.Ioo (0:ℝ) (1 / 2) ∧
            |(r - W.edgeDensity) - 2 * Dd d r (zetaFun d r)
                * c W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card)|
              ≤ C * (r - W.edgeDensity) ^ 2 ∧
            |c W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card)
                - lambdaGlobal d p r / (2 * Dd d r (zetaFun d r) * AHGlobal H d r)|
              ≤ C * lambdaGlobal d p r ^ 2 ∧
            |q22 W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card)
                - (r - (zetaFun d r ^ d - r ^ d)
                  / ((d : ℝ) * r ^ (d - 1) * Dd d r (zetaFun d r) * AHGlobal H d r)
                  * lambdaGlobal d p r)|
              ≤ C * lambdaGlobal d p r ^ 2 ∧
            |q12 W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card)
                - zetaFun d r| ≤ C * lambdaGlobal d p r ∧
            |q11 W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card)
                - q11 r 0| ≤ C * lambdaGlobal d p r := by
  obtain ⟨M, hr₀U, -⟩ := lz_boundary_arcs hd hr₀0 hr₀1 hr₀
  obtain ⟨ρ, η, C, κ, hρ0, hη0, hC0, hκ0, Dl, q11, q12, q22, c, hbase, ⟨Δ, hΔ0, hKRS⟩,
    hmain⟩ := parameter_asymptotics_zeta hd M H hreg hm hr₀U hr₀
  refine ⟨ρ, η, C, κ, Δ, hρ0, hη0, hC0, hκ0, hΔ0, q11, q12, q22, c, fun r hr => ?_,
    fun r hr p hp_lo hp_hi => ?_⟩
  · obtain ⟨-, hrex, hr0, hr1, hc0, hq22, hq11, hz, -, hκ⟩ := hbase r hr
    exact ⟨hr0, hr1, hrex, hc0, hq22, hz, hq11, by rwa [← hz], hKRS r hr⟩
  · obtain ⟨hrU, -, -, -, -, -, -, hz, -, -⟩ := hbase r hr
    rw [pcGlobal_eq_pc hd M hrU] at hp_lo hp_hi
    obtain ⟨-, -, -, -, ε, θ, hε, hθ, hedge, ⟨Wstar, -, -, hWrel⟩, ⟨B, hBf, hBo, hBae⟩, hcI,
      hdel, hcexp, hq22, hq12, hq11⟩ := hmain r hr p hp_lo hp_hi
    have hBe : B.edgeDensity = ε := hedge B hBf hBo
    -- every optimizer is a relabelling of `B`
    obtain ⟨σB, hσB, hBW⟩ := hWrel B hBf hBo
    obtain ⟨τ, hτ, hWB⟩ := exists_relabel_symm hσB hBW
    refine ⟨B, hBf, hBo, fun W' hW'f hW'o => ?_, ?_⟩
    · obtain ⟨σ', hσ', h'⟩ := hWrel W' hW'f hW'o
      exact ⟨fun x => τ (σ' x), hτ.comp hσ', ae_relabel_trans hσ'.measurePreserving h' hWB⟩
    · rw [hBe, ← hθ]
      rw [AH_eq_AHGlobal H hd M hrU, lambdaDisp_eq_lambdaGlobal hd M hrU, hz] at hcexp hq22
      rw [lambdaDisp_eq_lambdaGlobal hd M hrU] at hq12 hq11
      rw [hz] at hdel hq12
      have hδ : r - ε = Dl (p, r) := by rw [hε]; ring
      rw [hδ]
      exact ⟨hBae, hcI, hdel, hcexp, hq22, hq12, hq11⟩

/-- **The case `d = 2` of `eq:optimizer-block-size`** (the triangle case in the introduction).
For a `2`-regular `H` and `r₀ ≠ 1/2`, the smaller block of the optimizer satisfies
`c(p,r) = r λ(p,r)/((2r-1)² A_H(r)) + O(λ(p,r)²)` on `U`, because `ζ_2(r) = 1 - r` and
`2D_2(r,1-r) = (2r-1)²/r`. -/
theorem bipodal_block_size_two {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ x, H.degree x = 2)
    (hm : 1 ≤ H.edgeFinset.card) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1)
    (hr₀ : r₀ ≠ 1 / 2) :
    ∃ ρ η C : ℝ, 0 < ρ ∧ 0 < η ∧ 0 ≤ C ∧
      ∃ q11 q12 q22 c : ℝ → ℝ → ℝ,
        ∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, pcGlobal 2 r - η < p → p < pcGlobal 2 r →
          ∃ W : Graphon, Feasible H r W ∧ W.Ip p = phiVar H p r ∧
            (∀ W' : Graphon, Feasible H r W' → W'.Ip p = phiVar H p r →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) ∧
            (∀ᵐ z ∂gμ, W.toFun z.1 z.2
              = bipodalValue
                  (Set.Icc 0 (c W.edgeDensity (r ^ H.edgeFinset.card
                    - W.edgeDensity ^ H.edgeFinset.card)))
                  (q11 W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card))
                  (q12 W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card))
                  (q22 W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card))
                  z) ∧
            c W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card)
              ∈ Set.Ioo (0:ℝ) (1 / 2) ∧
            |c W.edgeDensity (r ^ H.edgeFinset.card - W.edgeDensity ^ H.edgeFinset.card)
                - r * lambdaGlobal 2 p r / ((2 * r - 1) ^ 2 * AHGlobal H 2 r)|
              ≤ C * lambdaGlobal 2 p r ^ 2 := by
  have hd : 2 ≤ 2 := le_rfl
  have hr₀' : r₀ ≠ rStar 2 := by
    rw [show rStar 2 = 1 / 2 by unfold rStar; norm_num]; exact hr₀
  obtain ⟨ρ, η, C, κ, Δ, hρ0, hη0, hC0, -, -, q11, q12, q22, c, hbase, hmain⟩ :=
    bipodal_parameter_expansions hd H hreg hm hr₀0 hr₀1 hr₀'
  refine ⟨ρ, η, C, hρ0, hη0, hC0, q11, q12, q22, c, fun r hr p hp_lo hp_hi => ?_⟩
  obtain ⟨hr0, hr1, -⟩ := hbase r hr
  obtain ⟨W, hWf, hWo, huniq, hae, hcI, -, hcexp, -⟩ := hmain r hr p hp_lo hp_hi
  refine ⟨W, hWf, hWo, huniq, hae, hcI, ?_⟩
  -- `2 D_2(r, 1-r) A = (2r-1)² A / r`
  have hr0' : r ≠ 0 := ne_of_gt hr0
  have hDd : Dd 2 r (zetaFun 2 r) = (2 * r - 1) ^ 2 / (2 * r) := by
    rw [zetaFun_two hr0 hr1]
    unfold Dd
    field_simp
    ring
  have hcoef : lambdaGlobal 2 p r / (2 * Dd 2 r (zetaFun 2 r) * AHGlobal H 2 r)
      = r * lambdaGlobal 2 p r / ((2 * r - 1) ^ 2 * AHGlobal H 2 r) := by
    rw [hDd, show 2 * ((2 * r - 1) ^ 2 / (2 * r)) * AHGlobal H 2 r
        = (2 * r - 1) ^ 2 * AHGlobal H 2 r / r by field_simp, div_div_eq_mul_div, mul_comm]
  rw [← hcoef]
  exact hcexp

end UpperTailOptimizers
