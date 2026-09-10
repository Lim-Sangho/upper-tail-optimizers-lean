import UpperTailOptimizers.KRRS.Reduced

/-!
# The two Kenyon–Radin–Ren–Sadun inputs of Appendix A

Appendix A of `paper/bipodal_optimizer.tex` (Appendix A) opens with the sentence

> We use only the statements of \[KRR–S, Theorems 1.1 and 3.3\].

This file packages the external inputs used by that argument. It carries two axioms,
based on the quoted
theorem of Kenyon–Radin–Ren–Sadun, *Bipodal structure in oversaturated random graphs*
(arXiv:1509.05370; IMRN 2018, `kenyon2014entropy`).  Everything else the appendix uses is
proved: the scalar nondegeneracy of `ψ_d` (`KRRS/PsiNondeg.lean`), the parameter chart and
its derivatives (`KRRS/Chart.lean`, `KRRS/TCalc.lean`, `KRRS/SCalc.lean`), the analytic
pode-size chart (`KRRS/CChart.lean`), the desingularized stationarity system and its
implicit-function family, and the final assembly (`KRRS/Main.lean`).

## What is deliberately *not* assumed

* Uniformity in `ε` of the surplus window — it is derived below, as `exists_uniform_strip`,
  from `region_open`, exactly as in the appendix's paragraph 4, which notes that the step
  "uses only the theorem statement"; the paper performs it in its summary of KRR–S, ahead of
  `thm:krrs-analytic-extension`, whose own added content is instead the two-sided analytic continuation of the
  parameter map through `ϑ = 0`. KRR–S `thm:krrs-bipodality` is pointwise in `ε`: their `τ₀` depends
  on `ε`, which is why `h` below is a *function*.
* Interiority of the block densities on the whole region, and `0 < c < 1`: only
  `Set.Icc 0 1` membership is assumed (it is what makes the parameters describe a
  graphon at all).  Strict interiority near the degenerate boundary is derived from the
  one-sided limits, and `0 < c` from the strict surplus via `tBip_zero`.
* The `O(ϑ)` rate for `c` that KRR–S also state: the appendix derives its own, uniform in
  `ε`, from analyticity of the two-sided extension.

Existence of the maximizer, by contrast, *is* part of what is assumed: KRR–S `thm:krrs-bipodality`
asserts that the maximizer at `(ε,τ)` exists and is unique, and `optimizer` below
records that. This fixed-edge, fixed-subgraph-density entropy problem differs from
the upper-tail minimization problem: `Graphon/Attainment.lean` proves attainment for
the latter by the direct method.

## A note on `ψ_d` at `z = ε`

`psiD d ε ε = 0 / 0 = 0` under Lean's junk-value convention, whereas the paper fills the
removable singularity with the honest limit.  Every clause below that quantifies over `z`
therefore carries the guard `z ≠ ε`.  Without it `isMax` would be *false*, and assuming a
false statement here would silently trivialise the development.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

/-! ### KRR–S `thm:krrs-cross-density`: the cross-density selector `ζ_d` -/

/-- **Data from Kenyon–Radin–Ren–Sadun, Theorem 3.3**, recorded in the paper as
`thm:krrs-cross-density`. In the notation used here:

> For fixed `k` and `ε`, there is a unique solution to `∂ψ_k(ε,ε̃)/∂ε̃ = 0`, which we
> denote `ε̃ = ζ_k(ε)`.  The function `ζ_k` is strictly decreasing, with nowhere-vanishing
> derivative and with fixed point at `ε = (k-1)/k`.  Furthermore, `ζ_k` is an involution.

together with the variational characterisation of `ζ_d` as the *maximizer* of
`z ↦ ψ_d(ε,z)`, which is how their §4 produces it and how `paper/bipodal_optimizer.tex` introduces
it in \Cref{sec:preliminaries}.

Only `mem_Ioo`, `isMax`, `strictAntiOn` and `involutive`/`fixed` are consumed; the
"nowhere-vanishing derivative" clause is not transcribed, because the development never
differentiates `ζ_d` — and an unused clause is an unnecessary risk of asserting something
false. -/
structure KRRSZeta (d : ℕ) where
  /-- The KRR–S cross density `ζ_d`. -/
  zeta : ℝ → ℝ
  /-- `ζ_d` maps interior densities to interior densities. -/
  mem_Ioo : ∀ ε ∈ Set.Ioo (0:ℝ) 1, zeta ε ∈ Set.Ioo (0:ℝ) 1
  /-- `ζ_d(ε)` maximises `z ↦ ψ_d(ε,z)` over `(0,1)`.  The guard `z ≠ ε` is Lean's, not
  the paper's: see the module docstring. -/
  isMax : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ z ∈ Set.Ioo (0:ℝ) 1, z ≠ ε →
    psiD d ε z ≤ psiD d ε (zeta ε)
  /-- `ζ_d` is strictly decreasing. -/
  strictAntiOn : StrictAntiOn zeta (Set.Ioo (0:ℝ) 1)
  /-- `ζ_d` is an involution. -/
  involutive : ∀ ε ∈ Set.Ioo (0:ℝ) 1, zeta (zeta ε) = ε
  /-- `ζ_d` fixes the exceptional density `(d-1)/d`. -/
  fixed : zeta (rStar d) = rStar d

/-- **Kenyon–Radin–Ren–Sadun, Theorem 3.3 and the maximizer characterisation in §4**
(arXiv:1509.05370); see `thm:krrs-cross-density` and the paragraph following it in the paper.
The complete assumed content is the collection of fields of `KRRSZeta`. -/
axiom krrs_thm33 (d : ℕ) (hd : 2 ≤ d) : Nonempty (KRRSZeta d)

/-! ### Consequences of the `thm:krrs-cross-density` input

The paper's "since `U` avoids the exceptional density, one has `ζ_d(ε) ≠ ε`" and the
`z₀ ≠ ε_*` used in paragraph 1 are *derived* here, not assumed: a strictly decreasing map
has at most one fixed point, and `(d-1)/d` is one. -/

theorem rStar_mem_Ioo {d : ℕ} (hd : 2 ≤ d) : rStar d ∈ Set.Ioo (0:ℝ) 1 := by
  have hd0 : (0:ℝ) < (d : ℝ) := by
    have : (0:ℕ) < d := by omega
    exact_mod_cast this
  have hd1 : (1:ℝ) ≤ (d : ℝ) - 1 := by
    have : (2:ℕ) ≤ d := hd
    have : (2:ℝ) ≤ (d : ℝ) := by exact_mod_cast this
    linarith
  constructor
  · unfold rStar
    positivity
  · unfold rStar
    rw [div_lt_one hd0]
    linarith

/-- `ζ_d(ε) ≠ ε` away from the exceptional density: a strictly decreasing function has at
most one fixed point, and `ζ_d` already fixes `(d-1)/d`. -/
theorem KRRSZeta.ne_self {d : ℕ} (hd : 2 ≤ d) (Z : KRRSZeta d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0:ℝ) 1) (hne : ε ≠ rStar d) : Z.zeta ε ≠ ε := by
  intro hfix
  rcases lt_trichotomy ε (rStar d) with hlt | heq | hgt
  · have := Z.strictAntiOn hε (rStar_mem_Ioo hd) hlt
    rw [hfix, Z.fixed] at this
    exact absurd this (not_lt.mpr hlt.le)
  · exact hne heq
  · have := Z.strictAntiOn (rStar_mem_Ioo hd) hε hgt
    rw [hfix, Z.fixed] at this
    exact absurd this (not_lt.mpr hgt.le)

/-- `ζ_d(ε) ≠ (d-1)/d` away from the exceptional density: apply the involution. -/
theorem KRRSZeta.ne_rStar {d : ℕ} (Z : KRRSZeta d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0:ℝ) 1) (hne : ε ≠ rStar d) : Z.zeta ε ≠ rStar d := by
  intro hz
  exact hne (by rw [← Z.involutive ε hε, hz, Z.fixed])

/-! ### KRR–S `thm:krrs-bipodality`: the bipodal optimizer on a positive-surplus region -/

/-- The positive-surplus region of KRR–S `thm:krrs-bipodality`, in the appendix's coordinates
`(ε, ϑ)` with `τ = ε^m + ϑ`.  Their statement cuts it out, over each nonexceptional `ε`,
by `ε^m < τ < τ₀(ε)`; here `h ε = τ₀(ε) - ε^m`, so the fibre over `ε` is the interval
`(0, h ε)` — the property `eq:krrs-domain-fibres` that paragraph 4 turns into a window
uniform in `ε`. -/
def krrsRegion (d : ℕ) (h : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ Set.Ioo (0:ℝ) 1 ∧ p.1 ≠ rStar d ∧ 0 < p.2 ∧ p.2 < h p.1}

/-- **Data from Kenyon–Radin–Ren–Sadun, Theorem 1.1**, recorded in the paper as
`thm:krrs-bipodality`. In the notation used here:

> Let `H` be a `k`-starlike graph with `ℓ ≥ 2` edges.  Let `ε ∈ (0,1)` be any point other
> than `(k-1)/k`.  Then there is a number `τ₀ > ε^ℓ` (depending on `ε`) such that for all
> `τ ∈ (ε^ℓ, τ₀)`, the entropy-maximizing graphon at `(ε,τ)` is unique (up to
> measure-preserving transformations of `[0,1]`) and bipodal.  The parameters
> `(c, p₁₁, p₁₂, p₂₂)` are analytic functions of `ε` and `τ` on the region
> `ε ≠ (k-1)/k`, `τ ∈ (ε^ℓ, τ₀(ε))`.  Furthermore, as `τ ↘ ε^ℓ` we have that
> `p₂₂ → ε`, `p₁₂ → ζ_k(ε)`, `p₁₁` satisfies `S₀'(p₁₁) = 2S₀'(p₁₂) - S₀'(p₂₂)`, and
> `c = O(τ - ε^ℓ)`.

Written in the coordinates `(ε, ϑ)`, `τ = ε^m + ϑ`.  `region_open` is the appendix's
reading of "the parameters are analytic functions on the region". It is an explicit
assumption: the `analytic` field, which asserts `AnalyticAt` at each point of the region,
does not itself imply that the region is open. The `O(ϑ)` clause is weakened to `c → 0`, which is all the
appendix consumes — its own, `ε`-uniform, `O(ϑ)` bound is derived downstream. -/
structure KRRSOptimizer {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (Z : KRRSZeta d) where
  /-- The length `τ₀(ε) - ε^m` of the surplus interval over `ε`. -/
  hwin : ℝ → ℝ
  /-- The four bipodal parameters as functions of `(ε, ϑ)`. -/
  q11 : ℝ → ℝ → ℝ
  q12 : ℝ → ℝ → ℝ
  q22 : ℝ → ℝ → ℝ
  cpar : ℝ → ℝ → ℝ
  /-- The limiting first-pode internal density. -/
  q110 : ℝ → ℝ
  hwin_pos : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d → 0 < hwin ε
  /-- Openness assumed in addition to `analytic`, following the appendix's reading of
  the KRR–S domain. Used to derive the uniform positive-surplus strip. -/
  region_open : IsOpen (krrsRegion d hwin)
  /-- The parameters take values in `[0,1]`, so that they describe a graphon. -/
  mem_Icc : ∀ p ∈ krrsRegion d hwin,
    q11 p.1 p.2 ∈ Set.Icc (0:ℝ) 1 ∧ q12 p.1 p.2 ∈ Set.Icc (0:ℝ) 1 ∧
      q22 p.1 p.2 ∈ Set.Icc (0:ℝ) 1 ∧ cpar p.1 p.2 ∈ Set.Icc (0:ℝ) 1
  /-- Joint real-analyticity of the four parameters on the region. -/
  analytic : ∀ p ∈ krrsRegion d hwin,
    AnalyticAt ℝ (fun w : ℝ × ℝ => q11 w.1 w.2) p ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => q12 w.1 w.2) p ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => q22 w.1 w.2) p ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => cpar w.1 w.2) p
  /-- On the region the entropy maximizer at `(ε, ε^m + ϑ)` exists, is the bipodal graphon
  with these parameters, and is unique up to a measure-preserving relabelling. -/
  optimizer : ∀ p ∈ krrsRegion d hwin,
    ∃ W : Graphon, W.edgeDensity = p.1 ∧
      W.tDensity H = p.1 ^ H.edgeFinset.card + p.2 ∧
      (∀ᵐ z ∂gμ, W.toFun z.1 z.2
        = bipodalValue (Set.Icc 0 (cpar p.1 p.2)) (q11 p.1 p.2) (q12 p.1 p.2)
            (q22 p.1 p.2) z) ∧
      (∀ W' : Graphon, W'.edgeDensity = p.1 →
        W'.tDensity H = p.1 ^ H.edgeFinset.card + p.2 → W'.entropy ≤ W.entropy) ∧
      (∀ W' : Graphon, W'.edgeDensity = p.1 →
        W'.tDensity H = p.1 ^ H.edgeFinset.card + p.2 → W'.entropy = W.entropy →
        ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
          ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2))
  /-- `q₁₁ → q₁₁⁰(ε)` as `ϑ ↘ 0`, where `q₁₁⁰(ε)` is the interior solution of the KRR–S
  boundary relation `S₀'(q₁₁) = 2S₀'(q₁₂) - S₀'(q₂₂)`. -/
  q110_mem : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d → q110 ε ∈ Set.Ioo (0:ℝ) 1
  q110_rel : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d →
    dS0 (q110 ε) = 2 * dS0 (Z.zeta ε) - dS0 ε
  tendsto_q11 : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d →
    Tendsto (fun ϑ => q11 ε ϑ) (𝓝[>] (0:ℝ)) (𝓝 (q110 ε))
  /-- `q₁₂ → ζ_d(ε)` as `ϑ ↘ 0`. -/
  tendsto_q12 : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d →
    Tendsto (fun ϑ => q12 ε ϑ) (𝓝[>] (0:ℝ)) (𝓝 (Z.zeta ε))
  /-- `q₂₂ → ε` as `ϑ ↘ 0`. -/
  tendsto_q22 : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d →
    Tendsto (fun ϑ => q22 ε ϑ) (𝓝[>] (0:ℝ)) (𝓝 ε)
  /-- `c → 0` as `ϑ ↘ 0` (their `c = O(τ - ε^ℓ)`, weakened to what is used). -/
  tendsto_c : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ε ≠ rStar d →
    Tendsto (fun ϑ => cpar ε ϑ) (𝓝[>] (0:ℝ)) (𝓝 0)

/-- **Kenyon–Radin–Ren–Sadun, `thm:krrs-bipodality`** (arXiv:1509.05370, Theorem 1.1).

The hypotheses are the paper's: `H` is `d`-regular with at least two edges — a special
case of their `d`-starlike, which allows degree-`1` vertices as well — and `d ≥ 2`.
The complete assumed content is the collection of fields of `KRRSOptimizer`, including
`region_open` and the one-sided measure-preserving-map formulation of uniqueness. -/
axiom krrs_thm11 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) (Z : KRRSZeta d) : Nonempty (KRRSOptimizer H d Z)

/-! ### The uniform positive-surplus strip (Appendix A, paragraph 4)

The appendix's `eq:krrs-uniform-domain`: openness of the region plus the interval shape
of its fibres upgrades a single point of the region to a *rectangle* whose surplus window
does not depend on `ε`.  This is the only place where uniformity in `ε` is manufactured, and
it uses nothing but `region_open`, `hwin_pos` and the definition of `krrsRegion`.

It is bookkeeping over the KRR–S *statement*, not the content `thm:krrs-analytic-extension` adds: the appendix
notes that the step "uses only the theorem statement and not any localization argument from
its proof", and the paper performs it in its summary of KRR–S, ahead of `thm:krrs-analytic-extension`.  What
`thm:krrs-analytic-extension` adds is the two-sided analytic continuation of the parameter map through `ϑ = 0`,
which KRR–S do not provide because they define it only for `ϑ > 0`; that is built in
`KRRS/Family.lean` and identified with the KRR–S parameters in `KRRS/Main.lean`. -/

theorem exists_uniform_strip {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {d : ℕ} {Z : KRRSZeta d} (O : KRRSOptimizer H d Z)
    {ε₀ : ℝ} (hε₀ : ε₀ ∈ Set.Ioo (0:ℝ) 1) (hne : ε₀ ≠ rStar d) :
    ∃ (a Δ : ℝ), 0 < a ∧ 0 < Δ ∧
      ∀ ε, |ε - ε₀| < a → ∀ ϑ, 0 < ϑ → ϑ < Δ → (ε, ϑ) ∈ krrsRegion d O.hwin := by
  classical
  -- a point of the region over `ε₀`
  have hpos : 0 < O.hwin ε₀ := O.hwin_pos ε₀ hε₀ hne
  obtain ⟨t0, ht00, ht0h⟩ : ∃ t : ℝ, 0 < t ∧ t < O.hwin ε₀ :=
    ⟨O.hwin ε₀ / 2, by linarith, by linarith⟩
  have hmem : (ε₀, t0) ∈ krrsRegion d O.hwin := ⟨hε₀, hne, ht00, ht0h⟩
  -- openness gives a rectangle around it
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp O.region_open _ hmem
  refine ⟨min a t0, t0, lt_min ha ht00, ht00, ?_⟩
  intro ε hεa ϑ hϑ0 hϑΔ
  -- `(ε, t0)` is in the region, hence so is `(ε, ϑ)` for `0 < ϑ < t0`
  have hεa' : |ε - ε₀| < a := lt_of_lt_of_le hεa (min_le_left _ _)
  have hin : (ε, t0) ∈ krrsRegion d O.hwin := by
    refine hball ?_
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_self, abs_zero, max_lt_iff]
    exact ⟨hεa', ha⟩
  obtain ⟨hεI, hεne, -, hlt⟩ := hin
  exact ⟨hεI, hεne, hϑ0, lt_trans hϑΔ hlt⟩

end UpperTailOptimizers
