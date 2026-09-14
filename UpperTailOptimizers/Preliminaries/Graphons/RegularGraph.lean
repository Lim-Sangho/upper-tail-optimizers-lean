import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Elementary facts about finite regular graphs

Shared infrastructure for the whole formalisation of `paper/paper.tex`; not itself a
statement of the paper.  Low-level counting lemmas for a `d`-regular graph `H` with `m = |E(H)|` edges, placed
below `Preliminaries/Graphons/ExternalInputs.lean` so that every layer of the development can use them.

The one that matters most is `two_le_card_edgeFinset`: the paper's
`thm:krrs-analytic-extension` (Kenyon–Radin–Ren–Sadun) is stated for graphs with `m ≥ 2`, so the
Lean theorems formalising it (`kenyonRadinRenSadun` and its companions in `Preliminaries/KRRSAnalyticExtension/Main.lean`)
carry that hypothesis; `two_le_card_edgeFinset` discharges it at every call site from the
standing hypotheses `2 ≤ d`, `H` `d`-regular, `1 ≤ m`.

`nonempty_of_edge`, `regular_handshake` and `degree_le_card_edges` were previously stated
in `NonexceptionalEndpoint/QuadraticGrowth/QuadraticUpper.lean`; they live here now and are re-used there.
-/

namespace UpperTailOptimizers

/-- A graph with an edge has a vertex. -/
theorem nonempty_of_edge {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hm : 1 ≤ H.edgeFinset.card) : Nonempty V := by
  obtain ⟨e, _⟩ := Finset.card_pos.mp (by omega : 0 < H.edgeFinset.card)
  induction e using Sym2.ind with
  | _ x y => exact ⟨x⟩

/-- Handshake for a `d`-regular graph: `n·d = 2m`. -/
theorem regular_handshake {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) :
    Fintype.card V * d = 2 * H.edgeFinset.card := by
  have h := H.sum_degrees_eq_twice_card_edges
  simp only [hreg, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  exact h

/-- In a regular graph with an edge, the degree is at most the number of edges: the `d`
edges at a fixed vertex are distinct edges of `H`. -/
theorem degree_le_card_edges {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) : d ≤ H.edgeFinset.card := by
  obtain ⟨v₀⟩ := nonempty_of_edge H hm
  have h1 : H.degree v₀ = (H.edgeFinset.filter fun e => v₀ ∈ e).card := by
    rw [show (H.edgeFinset.filter fun e => v₀ ∈ e) = H.incidenceFinset v₀ from
      (H.incidenceFinset_eq_filter v₀).symm, SimpleGraph.card_incidenceFinset_eq_degree]
  rw [← hreg v₀, h1]
  exact Finset.card_filter_le _ _

/-- **A `d`-regular graph with `d ≥ 2` and at least one edge has at least two edges.**

This is the hypothesis `m = |E(H)| ≥ 2` of `thm:krrs-analytic-extension` of `paper/paper.tex`
(Kenyon–Radin–Ren–Sadun); it is *derivable* here, so the KRR–S theorems of `Preliminaries/KRRSAnalyticExtension/Main.lean`
can take it as a hypothesis at no cost to their call sites. -/
theorem two_le_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 1 ≤ H.edgeFinset.card) : 2 ≤ H.edgeFinset.card :=
  le_trans hd (degree_le_card_edges H hreg hm)

end UpperTailOptimizers
