import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.TDensityExpansion
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Defs

/-!
# The rank-one homomorphism-density identity (Section 5, `paper/sections/singular.tex`)

Section 5 works throughout with **rank-one** graphons `W = f ⊗ f`.  For a `d`-regular `H`
on `v = |V(H)|` vertices such a `W` satisfies the identity displayed, unlabelled, in
`sec:rank-one-stationary-family` just before `lem:stationary-rank-one-bipodality` (and used in
its two-block form in the `eq:block-stationarity` step of the proof of `lem:rank-one-kkt-family`,
`paper/sections/appendix_singular_endpoint.tex`),

`t(H, W) = (∫₀¹ f(x)^d dx)^v`,

which is what turns the graphon Lagrangian into the three-variable function of `(α, s, t)`
that the same step differentiates in `α` to reach `eq:block-proportion-balance` and
`eq:block-proportion-formula`.  The reason is purely combinatorial: for a
rank-one kernel the product over the edges of `H` factors through the vertices,

`∏_{e = xy ∈ E(H)} f(x) f(y) = ∏_{v ∈ V(H)} f(v)^{deg v}`,

and for a regular graph every exponent is the same `d`.

Section 5's candidates are the two-valued kernels `f = s·1_{[0,α]} + t·1_{(α,1]}`, whose
`f ⊗ f` is the project's `bipodalGraphon (Icc 0 α) _ (s²) (st) (t²)`.  For these the
identity reads `t(H, W) = (α s^d + (1-α) t^d)^v`, and the edge density is
`(α s + (1-α) t)²`.

## Contents

* `prod_edges_eq_prod_pow_degree` — the edge/vertex product identity
  `∏_{e = xy} g x · g y = ∏_v g v ^ deg v`, for an arbitrary real weight `g`;
* `blockVal_rankOne` — the two-block values of the rank-one kernel `f ⊗ f` with
  `f = s·1_A + t·1_{Aᶜ}`;
* `edgeProd_rankOne` — the edge factor of a labelling, `∏_v (τ v ? s : t)^d`;
* `tBip_rankOne` — the rank-one identity for the labelling polynomial,
  `tBip = (c s^d + (1-c) t^d)^{|V|}`;
* `tDensity_rankOne_two_block`, `edgeDensity_rankOne_two_block` — the graphon-level
  statements `t(H, W_{c,s,t}) = (c s^d + (1-c) t^d)^{|V|}` and
  `Edge(W_{c,s,t}) = (c s + (1-c) t)²`.
-/

namespace UpperTailOptimizers

open Finset

/-! ### The edge/vertex product identity -/

/-- **The rank-one edge product factors through the vertices**: for any weight `g` on the
vertices of a finite simple graph `H`,
`∏_{e = xy ∈ E(H)} g x · g y = ∏_{v} g v ^ deg(v)`.

This is the combinatorial core of the rank-one density identity of Section 5 (the display
`t(H, f ⊗ f) = (∫ f^d)^v`): each vertex `v` is counted once for every edge incident to it,
i.e. `deg v` times. -/
theorem prod_edges_eq_prod_pow_degree {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (g : V → ℝ) :
    ∏ e ∈ H.edgeFinset, Sym2.lift ⟨fun x y => g x * g y, fun _ _ => mul_comm _ _⟩ e
      = ∏ v, g v ^ H.degree v := by
  classical
  -- `g v ^ deg v` is the product of the constant `g v` over the edges at `v`
  have hpow : ∀ v : V, g v ^ H.degree v = ∏ _e ∈ H.incidenceFinset v, g v := by
    intro v
    rw [Finset.prod_const, SimpleGraph.card_incidenceFinset_eq_degree]
  -- double counting: swap the vertex and edge products
  have hcomm : (∏ v, ∏ _e ∈ H.incidenceFinset v, g v)
      = ∏ e ∈ H.edgeFinset, ∏ v ∈ Finset.univ.filter (fun v => v ∈ e), g v := by
    refine Finset.prod_comm' ?_
    intro v e
    rw [H.incidenceFinset_eq_filter v]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter]
    tauto
  rw [Finset.prod_congr rfl (fun v _ => hpow v), hcomm]
  -- an edge of a simple graph has exactly two, distinct, endpoints
  refine (Finset.prod_congr rfl fun e he => ?_).symm
  induction e using Sym2.ind with
  | _ x y =>
    have hadj : H.Adj x y := by
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hxy : x ≠ y := hadj.ne
    have hset : (Finset.univ.filter fun v => v ∈ s(x, y)) = {x, y} := by
      ext v
      simp [Sym2.mem_iff]
    rw [hset, Finset.prod_insert (by simpa using hxy), Finset.prod_singleton]
    rfl

/-! ### The rank-one two-valued kernel -/

/-- **The block values of the rank-one two-valued kernel.** For `f = s·1_A + t·1_{Aᶜ}` the
kernel `f ⊗ f` has value `s²` inside `A`, `s t` across and `t²` outside, i.e. exactly
`blockVal (s^2) (s*t) (t^2)`; and this is the product of the two endpoint values of `f`.
(Recall `blockVal a s q i j` is `a` when `i = j = true`, `q` when `i = j = false`, and `s`
otherwise.) -/
theorem blockVal_rankOne (s t : ℝ) (i j : Bool) :
    blockVal (s ^ 2) (s * t) (t ^ 2) i j
      = (if i then s else t) * (if j then s else t) := by
  cases i <;> cases j <;> simp [blockVal, sq, mul_comm]

/-- **The edge factor of a labelling for the rank-one two-valued kernel**, for `d`-regular
`H`: it is `∏_v (τ v ? s : t)^d`, independent of the graph beyond its regularity. -/
theorem edgeProd_rankOne {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) (s t : ℝ) (τ : V → Bool) :
    edgeProd H (s ^ 2) (s * t) (t ^ 2) τ = ∏ v, (if τ v then s else t) ^ d := by
  classical
  have hrw : edgeProd H (s ^ 2) (s * t) (t ^ 2) τ
      = ∏ e ∈ H.edgeFinset, Sym2.lift
          ⟨fun x y => (if τ x then s else t) * (if τ y then s else t),
            fun _ _ => mul_comm _ _⟩ e := by
    rw [edgeProd]
    refine Finset.prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ x y => exact blockVal_rankOne s t (τ x) (τ y)
  rw [hrw, prod_edges_eq_prod_pow_degree H fun v => if τ v then s else t]
  exact Finset.prod_congr rfl fun v _ => by rw [hreg v]

/-- The labelling weight `c^{k(τ)} (1-c)^{n-k(τ)}` as a product over the vertices.  This is
the measure-free counterpart of `prod_blockMeasure_Icc`; no bound on `c` is needed. -/
private theorem prod_ite_eq_weight {V : Type*} [Fintype V] (c : ℝ) (τ : V → Bool) :
    (∏ v, if τ v then c else 1 - c)
      = c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ) := by
  classical
  have hτc : trueCount τ = (Finset.univ.filter fun v => τ v = true).card := rfl
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (fun v => τ v = true)
  rw [Finset.card_univ] at hsum
  calc (∏ v, if τ v then c else 1 - c)
      = (∏ _v ∈ Finset.univ.filter fun v => τ v = true, c)
        * ∏ _v ∈ Finset.univ.filter fun v => ¬ τ v = true, (1 - c) := Finset.prod_ite _ _
    _ = c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ) := by
        rw [Finset.prod_const, Finset.prod_const, hτc]
        congr 2
        omega

/-- **The rank-one identity for the bipodal `H`-density polynomial** (Section 5, the display
`t(H, W) = (∫ f^d)^v` specialised to `f = s·1_{[0,c]} + t·1_{(c,1]}`): for a `d`-regular `H`,

`tBip H s² (st) t² c = (c s^d + (1-c) t^d)^{|V(H)|}`.

The `2^{|V|}` labellings collapse because the edge factor and the weight both factor
through the vertices. -/
theorem tBip_rankOne {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) (s t c : ℝ) :
    tBip H (s ^ 2) (s * t) (t ^ 2) c
      = (c * s ^ d + (1 - c) * t ^ d) ^ Fintype.card V := by
  classical
  -- each labelling's summand is a product over the vertices
  have hterm : ∀ τ : V → Bool, edgeProd H (s ^ 2) (s * t) (t ^ 2) τ
        * (c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ))
      = ∏ v, if τ v then c * s ^ d else (1 - c) * t ^ d := by
    intro τ
    rw [edgeProd_rankOne H hreg s t τ, ← prod_ite_eq_weight c τ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    cases τ v <;> simp [mul_comm]
  rw [tBip, Finset.sum_congr rfl fun τ _ => hterm τ]
  -- expand the product of sums over the two blocks
  have hpi : (Fintype.piFinset fun _ : V => (Finset.univ : Finset Bool)) = Finset.univ :=
    Fintype.piFinset_univ
  have hprod := Finset.prod_univ_sum (fun _ : V => (Finset.univ : Finset Bool))
    (fun (_ : V) (b : Bool) => if b then c * s ^ d else (1 - c) * t ^ d)
  rw [hpi] at hprod
  rw [← hprod]
  simp only [Fintype.sum_bool, if_true, if_false, Bool.false_eq_true]
  rw [Finset.prod_const, Finset.card_univ]

/-! ### The graphon-level statements -/

/-- **The rank-one homomorphism-density identity for the two-block candidates of Section 5**:
for a `d`-regular `H` and the graphon `W = f ⊗ f` with `f = s·1_{[0,c]} + t·1_{(c,1]}`,

`t(H, W) = (c s^d + (1-c) t^d)^{|V(H)|}`.

This is the unlabelled display in the proof of `lem:rank-one-kkt-family`
(`paper/sections/appendix_singular_endpoint.tex`), used in the `eq:block-stationarity` step to
restrict the graphon Lagrangian to the bipodal family before differentiating in `α`. -/
theorem tDensity_rankOne_two_block {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {s t c : ℝ}
    (h11 : s ^ 2 ∈ Set.Icc (0:ℝ) 1) (h12 : s * t ∈ Set.Icc (0:ℝ) 1)
    (h22 : t ^ 2 ∈ Set.Icc (0:ℝ) 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (bipodalGraphon (Set.Icc 0 c) measurableSet_Icc (s ^ 2) (s * t) (t ^ 2)
        h11 h12 h22).tDensity H
      = (c * s ^ d + (1 - c) * t ^ d) ^ Fintype.card V := by
  rw [tBip_eq_tDensity H h11 h12 h22 hc0 hc1, tBip_rankOne H hreg]

/-- **The matching edge density of the two-block rank-one candidate**:
`Edge(W) = (c s + (1-c) t)²`, i.e. the `d = 1`, `|V| = 2` shape of
`tDensity_rankOne_two_block`. -/
theorem edgeDensity_rankOne_two_block {s t c : ℝ}
    (h11 : s ^ 2 ∈ Set.Icc (0:ℝ) 1) (h12 : s * t ∈ Set.Icc (0:ℝ) 1)
    (h22 : t ^ 2 ∈ Set.Icc (0:ℝ) 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (bipodalGraphon (Set.Icc 0 c) measurableSet_Icc (s ^ 2) (s * t) (t ^ 2)
        h11 h12 h22).edgeDensity
      = (c * s + (1 - c) * t) ^ 2 := by
  rw [bipodalGraphon_edgeDensity, unitμ_Icc_toReal hc0 hc1]
  ring

end UpperTailOptimizers
