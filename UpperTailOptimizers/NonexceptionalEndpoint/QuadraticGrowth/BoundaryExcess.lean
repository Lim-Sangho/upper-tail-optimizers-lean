import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.GraphonLower
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.QuadraticUpper
import UpperTailOptimizers.NonexceptionalEndpoint.LocalReduction.Main

/-!
# The boundary excess has a non-degenerate quadratic minimum (`thm:positive-second-variation`)

The boundary excess of `paper/paper.tex` (eq. `eq:boundary-excess`) is

`G_r(δ) = I_{pc(r),r}(r - δ) - J_{pc(r)}(r)`,

the extra entropy cost, at the boundary point `p = pc(r)`, of forcing edge density
`r - δ` while keeping the `H`-density at the constant-graphon level `r^m`.  In the
Lean development `I_{p,r}` is `reducedObjectiveReal` (`NonexceptionalEndpoint/LocalReduction/Main.lean`).

**`thm:positive-second-variation` (`boundaryExcess_quadratic`)** — the quantitative core of the paper's
Theorem "Universal positivity of the scalar second variation": uniformly for `r` in a
compact subarc `K`,

`C δ² ≤ G_r(δ) ≤ C' δ²` for `0 < δ < δ₀`, with `C, C' > 0`.

This is exactly the two-sided bound (`C_{d,I}δ² ≤ G_r(δ) ≤ C_{H,I}δ²` in the paper) from which
the paper concludes that the Taylor expansion of the (analytic) boundary excess begins in degree
exactly two, with `A_H(r) = lim_{δ↓0} 2G_r(δ)/δ² > 0`.  The paper then obtains a uniform lower
bound `a₀ = A_H(r₀)/2` by continuity after shrinking `I`; here `A_H(r) ∈ [2C, 2C']` gives
`A_H > 0` uniformly on `K` directly.

The proof combines the quadratic lower bound for graphons (`prop:graphon-quadratic-bound`,
`quadratic_lower_graphon`) — applied to **every** graphon in the fixed-`(e, t_H)`
constraint set, so that no attainment or Kenyon–Radin–Ren–Sadun input is needed on
this side — with the bipodal competitor of `lem:bipodal-quadratic-bound` (`quadratic_upper`), whose
entropy is a lower bound for the entropy envelope `S_H`.  Consequently the theorem
consumes only the `generalized_holder` axiom (through `prop:graphon-quadratic-bound`), and **not**
`kenyonRadinRenSadun` or `lubetzkyZhao`.

The remaining (qualitative) part of the paper's `thm:positive-second-variation` — that `G_r(δ)` agrees
for small `δ > 0` with a function analytic in `δ`, so that the second-variation
coefficient `A_H` is well defined and equals the limit `2 G_r(δ)/δ²` — rests on the
analytic parametrization clause of `thm:krrs-analytic-extension` (KRRS), the theorem
`kenyonRadinRenSadunAnalytic` of `Preliminaries/KRRSAnalyticExtension/Main.lean`.  That part is proved
in `NonexceptionalEndpoint/QuadraticGrowth/AnalyticExcess.lean` (`boundaryExcess_taylor`), on top of the
positivity established here.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Set

/-- **The boundary excess** `G_r(δ) = I_{pc(r),r}(r-δ) - J_{pc(r)}(r)`
(eq. `eq:boundary-excess` of `paper/paper.tex`). -/
noncomputable def boundaryExcess {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (M : LZBoundaryArc d) (r δ : ℝ) : ℝ :=
  reducedObjectiveReal H (M.pc r) (r - δ) (r ^ H.edgeFinset.card) - Jp (M.pc r) r

/-- **`thm:positive-second-variation`, quantitative form.**
Uniformly for `r` in a compact subarc `K` of a Lubetzky–Zhao boundary arc there are `C, C' > 0` and
`δ₀ > 0` with

`C δ² ≤ G_r(δ) ≤ C' δ²` for all `0 < δ < δ₀`.

In particular the boundary excess has a non-degenerate quadratic minimum at `δ = 0`:
any analytic extension of `G_r` has vanishing first derivative and second derivative
`A_H(r) ∈ [2C, 2C']` at `δ = 0`, uniformly positive on `K`. -/
theorem boundaryExcess_quadratic {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ C C' δ₀ : ℝ, 0 < C ∧ 0 < C' ∧ 0 < δ₀ ∧ ∀ r ∈ K, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      C * δ ^ 2 ≤ boundaryExcess H M r δ ∧ boundaryExcess H M r δ ≤ C' * δ ^ 2 := by
  obtain ⟨C, hC, hlow⟩ := quadratic_lower_graphon hd M hK hKc hKne H hreg hm
  obtain ⟨C', δ₀, hC', hδ₀, hupp⟩ := quadratic_upper hd M hK hKc hKne H hreg hm
  refine ⟨C, C', δ₀, hC, hC', hδ₀, ?_⟩
  intro r hr δ hδ0 hδlt
  obtain ⟨hpc0, hpcr, hr1, _, _, _⟩ := M.ordering r (hK hr)
  have hpc1 : M.pc r < 1 := lt_trans hpcr hr1
  -- the bipodal competitor of `lem:bipodal-quadratic-bound`
  obtain ⟨W, hWe, hWt, _, hWIp⟩ := hupp r hr δ hδ0 hδlt
  -- the fixed-(e, t_H) entropy constraint set
  have hWmem : W.entropy ∈ {s | ∃ W' : Graphon, W'.edgeDensity = r - δ
      ∧ W'.tDensity H = r ^ H.edgeFinset.card ∧ W'.entropy = s} := ⟨W, hWe, hWt, rfl⟩
  have hbdd := entropyEnvelope_bddAbove H (r - δ) (r ^ H.edgeFinset.card)
  constructor
  · -- lower bound: every graphon in the constraint set pays `J + Cδ²`, so the
    -- entropy envelope is capped and the reduced objective is bounded below.
    have hcap : entropyEnvelopeReal H (r - δ) (r ^ H.edgeFinset.card)
        ≤ (-(Jp (M.pc r) r + C * δ ^ 2) - Real.log (1 - M.pc r)
            + (r - δ) * Real.log ((1 - M.pc r) / M.pc r)) / 2 := by
      refine csSup_le ⟨W.entropy, hWmem⟩ ?_
      rintro s ⟨W', hW'e, hW't, rfl⟩
      have hfeas : r ^ H.edgeFinset.card ≤ W'.tDensity H := le_of_eq hW't.symm
      have hIp : Jp (M.pc r) r + C * δ ^ 2 ≤ W'.Ip (M.pc r) :=
        hlow r hr δ hδ0.le W' hW'e hfeas
      have hent := W'.Ip_eq_entropy hpc0 hpc1
      rw [hW'e] at hent
      linarith
    rw [boundaryExcess, reducedObjectiveReal]
    linarith
  · -- upper bound: the competitor's entropy is a lower bound for the envelope, and
    -- its `I_p`-value is controlled by `lem:bipodal-quadratic-bound`.
    have hσ : W.entropy ≤ entropyEnvelopeReal H (r - δ) (r ^ H.edgeFinset.card) :=
      le_csSup hbdd hWmem
    have hent := W.Ip_eq_entropy hpc0 hpc1
    rw [hWe] at hent
    rw [boundaryExcess, reducedObjectiveReal]
    linarith

/-- The boundary excess is strictly positive for `0 < δ < δ₀`, uniformly on `K`:
the constant graphon is a strict local minimiser along the edge-density constraint. -/
theorem boundaryExcess_pos {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d)
    {K : Set ℝ} (hK : K ⊆ M.U) (hKc : IsCompact K) (hKne : K.Nonempty)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ r ∈ K, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      0 < boundaryExcess H M r δ := by
  obtain ⟨C, C', δ₀, hC, _, hδ₀, hbound⟩ :=
    boundaryExcess_quadratic hd M hK hKc hKne H hreg hm
  refine ⟨δ₀, hδ₀, fun r hr δ hδ0 hδlt => ?_⟩
  have h := (hbound r hr δ hδ0 hδlt).1
  have : 0 < C * δ ^ 2 := by positivity
  linarith

end UpperTailOptimizers
