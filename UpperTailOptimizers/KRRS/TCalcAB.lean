import UpperTailOptimizers.KRRS.SCalc
import UpperTailOptimizers.KRRS.TCalc

/-!
# The `c = 0` value of `∂_a𝒯̂/c²`, and the `b`-derivative of `𝒯̂`

`KRRS/TCalc.lean` proves that the `a`-derivative of the edge-constrained `H`-density is
*exactly* `c²` times the analytic function `Rda` (`hasDerivAt_That_a`).
This file supplies the two facts that paragraph 3 of Appendix A of `paper/bipodal_optimizer.tex`
(Appendix A) still needs from the `H`-density side:

* **`Rda_zero_indep_a`** — `Rda(ε,·,b,0)` is *constant*.  This is the sentence of the
  justification of `eq:krrs-density-expansion` that reads: a term with exactly two vertices in
  the first pode contains at most one factor `a`, because `H` is simple and those two
  vertices support at most one edge; terms with at least three vertices in the first pode
  are divisible by `c³`.  It is what makes the coefficient `B₁(ε,b)` of `a` in
  `eq:krrs-density-expansion` independent of `a`, hence `∂²_aM = S₀''(a)/𝒜(ε,b)²`
  `eq:krrs-coefficient-concavity` and the paragraph-3 Jacobian nondegenerate.
* **`hasDerivAt_That_b`** — `∂_b𝒯̂ = c · Rdb` with `Rdb` analytic (`analyticAt_Rdb`): the
  cross density `b` reaches `𝒯̂` only through labellings marking at least one vertex (whose
  weight carries `c`) and through `∂_bQ = -2c/(1-c)` (`hasDerivAt_Qmap_b`).

## Contents

* `edgeProd_eq_pow_bothCount` — **the combinatorial core**: `edgeProd` is `a^{A(τ)}` times
  an `a`-free factor, where `A(τ)` counts the edges of `H` internal to the set marked by
  `τ`.  In particular a labelling with at most one marked vertex never selects the
  first-block density;
* `bothCount_le_one_of_trueCount_eq_two` — simplicity of `H`: two marked vertices support
  at most one edge;
* `Rda_zero_indep_a` — the transfer of the two preceding facts to `KRRS/TCalc.lean`'s
  `Rda`;
* `partialB`, `Rdb`, `analyticAt_Rdb`, `hasDerivAt_That_b` — the `b`-derivative, mirroring
  the `partialA`/`ThatRem` pattern of `KRRS/TCalc.lean`.

The edge bookkeeping of a labelling (the per-edge block value, the "both endpoints marked"
predicate and its count `A(τ)`) and the `a`-partial of the `c²`-cofactor `tBipRem2` as an
explicit finite sum are file-private, as is the transfer step through `ThatRem`.
-/

namespace UpperTailOptimizers

open Real Filter Topology

/-! ### Edge factors of a labelling -/

/-- The block value seen by an edge `e` under the labelling `τ`: the factor of the product
that defines `edgeProd` in `Nondegeneracy/TDensityExpansion.lean`. -/
private noncomputable def edgeVal {V : Type*} (a s q : ℝ) (τ : V → Bool) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => blockVal a s q (τ x) (τ y),
    fun x y => blockVal_symm a s q (τ x) (τ y)⟩ e

@[simp] private theorem edgeVal_mk {V : Type*} (a s q : ℝ) (τ : V → Bool) (x y : V) :
    edgeVal a s q τ s(x, y) = blockVal a s q (τ x) (τ y) := rfl

/-- `edgeProd` is the product of the edge values. -/
private theorem edgeProd_eq_prod_edgeVal {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q : ℝ) (τ : V → Bool) :
    edgeProd H a s q τ = ∏ e ∈ H.edgeFinset, edgeVal a s q τ e := by
  simp only [edgeProd, edgeVal]

/-- Both endpoints of the edge are marked, i.e. the edge is internal to the first pode.
These are exactly the edges that see the first-block density `a`. -/
private def bothMarked {V : Type*} (τ : V → Bool) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun x y => τ x && τ y, fun x y => Bool.and_comm (τ x) (τ y)⟩ e

@[simp] private theorem bothMarked_mk {V : Type*} (τ : V → Bool) (x y : V) :
    bothMarked τ s(x, y) = (τ x && τ y) := rfl

/-- The number of edges of `H` internal to the set marked by `τ`: the exponent with which
the first-block density `a` occurs in `edgeProd`. -/
private noncomputable def bothCount {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (τ : V → Bool) : ℕ :=
  (H.edgeFinset.filter fun e => bothMarked τ e = true).card

/-- **Extraction of one block parameter from a product over the edges.**  If the edge factor
`f y e` equals `y` on the edges selected by `P` and does not depend on `y` off `P`, then the
product is `y^{#P}` times its value at `y = 1`. -/
private theorem prod_eq_pow_card_mul {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (P : Sym2 V → Bool) (f : ℝ → Sym2 V → ℝ) (x : ℝ)
    (hP : ∀ e, P e = true → ∀ y : ℝ, f y e = y)
    (hnP : ∀ e, P e = false → ∀ y z : ℝ, f y e = f z e) :
    ∏ e ∈ H.edgeFinset, f x e
      = x ^ (H.edgeFinset.filter fun e => P e = true).card * ∏ e ∈ H.edgeFinset, f 1 e := by
  have hsplit : ∀ y : ℝ, ∏ e ∈ H.edgeFinset, f y e
      = (∏ e ∈ H.edgeFinset.filter (fun e => P e = true), f y e)
        * ∏ e ∈ H.edgeFinset.filter (fun e => ¬ (P e = true)), f y e :=
    fun y => (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have hB : ∀ y : ℝ, (∏ e ∈ H.edgeFinset.filter (fun e => P e = true), f y e)
      = y ^ (H.edgeFinset.filter fun e => P e = true).card := by
    intro y
    rw [Finset.prod_congr rfl (fun e he => hP e (Finset.mem_filter.mp he).2 y),
      Finset.prod_const]
  have hN : (∏ e ∈ H.edgeFinset.filter (fun e => ¬ (P e = true)), f x e)
      = ∏ e ∈ H.edgeFinset.filter (fun e => ¬ (P e = true)), f 1 e :=
    Finset.prod_congr rfl fun e he => by
      have h := (Finset.mem_filter.mp he).2
      rw [Bool.not_eq_true] at h
      exact hnP e h x 1
  rw [hsplit x, hsplit 1, hB x, hB 1, one_pow, one_mul, hN]

/-- **The first-block density occurs in `edgeProd` exactly on the internal edges of the
marked set.**  The cofactor `edgeProd H 1 s q τ` does not involve `a`. -/
theorem edgeProd_eq_pow_bothCount {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q : ℝ) (τ : V → Bool) :
    edgeProd H a s q τ = a ^ bothCount H τ * edgeProd H 1 s q τ := by
  rw [edgeProd_eq_prod_edgeVal, edgeProd_eq_prod_edgeVal, bothCount]
  refine prod_eq_pow_card_mul H (bothMarked τ) (fun y e => edgeVal y s q τ e) a ?_ ?_
  · intro e he y
    induction e using Sym2.ind with
    | _ u v =>
      simp only [bothMarked_mk, Bool.and_eq_true] at he
      simp [blockVal, he.1, he.2]
  · intro e he y z
    induction e using Sym2.ind with
    | _ u v =>
      simp only [bothMarked_mk] at he
      have h' : ¬ (τ u = true ∧ τ v = true) := by
        rintro ⟨h1, h2⟩
        rw [h1, h2] at he
        simp at he
      show blockVal y s q (τ u) (τ v) = blockVal z s q (τ u) (τ v)
      cases hu : τ u <;> cases hv : τ v
      · rfl
      · rfl
      · rfl
      · exact absurd ⟨hu, hv⟩ h'

/-! ### The combinatorial core -/

/-- **Simplicity of `H`**: two marked vertices support at most one edge, so a labelling with
exactly two marked vertices contributes at most one factor `a`.  This is the sentence of
Appendix A justifying `eq:krrs-density-expansion`. -/
theorem bothCount_le_one_of_trueCount_eq_two {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {τ : V → Bool} (hτ : trueCount τ = 2) :
    bothCount H τ ≤ 1 := by
  rw [trueCount] at hτ
  obtain ⟨u, v, huv, hM⟩ := Finset.card_eq_two.mp hτ
  have hsub : (H.edgeFinset.filter fun e => bothMarked τ e = true) ⊆ {s(u, v)} := by
    intro e he
    obtain ⟨hmem, hb⟩ := Finset.mem_filter.mp he
    revert hb hmem
    induction e using Sym2.ind with
    | _ x y =>
      intro hmem hb
      have hadj : H.Adj x y := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem
      have hxy : x ≠ y := hadj.ne
      simp only [bothMarked_mk, Bool.and_eq_true] at hb
      have hx : x ∈ ({u, v} : Finset V) := by
        rw [← hM]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.1⟩
      have hy : y ∈ ({u, v} : Finset V) := by
        rw [← hM]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rw [Finset.mem_singleton]
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hxy
  calc bothCount H τ ≤ ({s(u, v)} : Finset (Sym2 V)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-! ### The `a`-partial of the `c²`-cofactor `tBipRem2` -/

/-- `tBipRem2` with the `a`-dependence of each edge factor made explicit. -/
private theorem tBipRem2_eq_pow_bothCount_sum {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (a s q c : ℝ) :
    tBipRem2 H a s q c
      = ∑ τ ∈ Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ),
          a ^ bothCount H τ * edgeProd H 1 s q τ
            * (c ^ (trueCount τ - 2) * (1 - c) ^ (Fintype.card V - trueCount τ)) := by
  simp only [tBipRem2]
  exact Finset.sum_congr rfl fun τ _ => by rw [edgeProd_eq_pow_bothCount]

/-- `∂_a tBipRem2`, as an explicit finite sum: only the exponent of `a` is differentiated. -/
private noncomputable def tBipRem2A {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q c : ℝ) : ℝ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ),
    (bothCount H τ : ℝ) * a ^ (bothCount H τ - 1) * edgeProd H 1 s q τ
      * (c ^ (trueCount τ - 2) * (1 - c) ^ (Fintype.card V - trueCount τ))

/-- `tBipRem2A` is the `a`-derivative of `tBipRem2`. -/
private theorem hasDerivAt_tBipRem2_a {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (s q c a : ℝ) :
    HasDerivAt (fun x => tBipRem2 H x s q c) (tBipRem2A H a s q c) a := by
  have hfun : (fun x => tBipRem2 H x s q c)
      = fun x : ℝ => ∑ τ ∈ Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ),
          x ^ bothCount H τ * edgeProd H 1 s q τ
            * (c ^ (trueCount τ - 2) * (1 - c) ^ (Fintype.card V - trueCount τ)) :=
    funext fun x => tBipRem2_eq_pow_bothCount_sum H x s q c
  rw [hfun, tBipRem2A]
  refine HasDerivAt.fun_sum fun τ _ => ?_
  exact ((hasDerivAt_pow _ a).mul_const _).mul_const _

/-- **At `c = 0` the `a`-partial of `tBipRem2` does not depend on `a`.**  Labellings with
three or more marked vertices carry a positive power of `c` and drop out; a labelling with
exactly two marked vertices has `bothCount ≤ 1`
(`bothCount_le_one_of_trueCount_eq_two`), so `edgeProd` is affine in `a` and its
`a`-derivative is `a`-free. -/
private theorem tBipRem2A_zero_indep_a {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a a' s q : ℝ) : tBipRem2A H a s q 0 = tBipRem2A H a' s q 0 := by
  simp only [tBipRem2A]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  have h2 : 2 ≤ trueCount τ := (Finset.mem_filter.mp hτ).2
  rcases eq_or_lt_of_le h2 with heq | hlt
  · -- exactly two marked vertices: at most one internal edge, so the `a`-power drops out
    have hb : bothCount H τ ≤ 1 := bothCount_le_one_of_trueCount_eq_two H heq.symm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  · -- at least three marked vertices: the weight carries a positive power of `c = 0`
    rw [zero_pow (show trueCount τ - 2 ≠ 0 by omega)]
    ring

/-! ### The `c = 0` value of `Rda` -/

/-- The `a`-partial of `KRRS/TCalc.lean`'s `ThatRem` at `c = 0` is the explicit sum
`tBipRem2A`.  At `c = 0` the edge-density solve is `Q = ε` (`Qmap_zero`), so the only
`a`-dependence left is the direct one. -/
private theorem partialA_ThatRem_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (ε a b : ℝ) :
    partialA (ThatRem H) (ε, a, b, 0) = tBipRem2A H a b ε 0 := by
  have h1 : HasDerivAt (fun x : ℝ => ThatRem H (ε, x, b, 0))
      (partialA (ThatRem H) (ε, a, b, 0)) a :=
    hasDerivAt_partialA (Φ := ThatRem H)
      (analyticAt_ThatRem H (p := ((ε, a, b, 0) : ℝ × ℝ × ℝ × ℝ)) (by norm_num))
  have hfun : (fun x : ℝ => ThatRem H (ε, x, b, 0)) = fun x : ℝ => tBipRem2 H x b ε 0 := by
    funext x
    simp [ThatRem]
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_tBipRem2_a H b ε 0 a)

/-- **The `c = 0` value of the quotient `∂_a𝒯̂/c²` does not depend on `a`.**

At `c = 0` the first two summands of `Rda` reduce to `-m ε^{m-1}`, which is `a`-free, and
the third is `tBipRem2A H a b ε 0`, which is `a`-free by `tBipRem2A_zero_indep_a`.  This is
exactly the claim of Appendix A that the coefficient `B₁(ε,b)` of `a` at order `c²` in
`eq:krrs-density-expansion` does not itself depend on `a`; it is what makes `∂²_aM` equal
`S₀''(a)/𝒜(ε,b)²` `eq:krrs-coefficient-concavity`, hence nonzero. -/
theorem Rda_zero_indep_a {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε b : ℝ) (a a' : ℝ) :
    Rda H d ε a b 0 = Rda H d ε a' b 0 := by
  simp only [Rda, Qmap_zero, partialA_ThatRem_zero]
  rw [tBipRem2A_zero_indep_a H a a' b ε]

/-! ### The `b`-derivative of `𝒯̂` is exactly `c` times an analytic function -/

/-- The partial derivative in the third slot `b` of a function of the four appendix
parameters `(ε,a,b,c)` — the `b`-analogue of `partialA` of `KRRS/TCalc.lean`. -/
noncomputable abbrev partialB (Φ : ℝ × ℝ × ℝ × ℝ → ℝ) (w : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  partialSlot (0, 0, 1, 0) Φ w

/-- The `b`-partial really is the derivative of `x ↦ Φ(ε,a,x,c)`. -/
theorem hasDerivAt_partialB {Φ : ℝ × ℝ × ℝ × ℝ → ℝ} {ε a b c : ℝ}
    (h : AnalyticAt ℝ Φ (ε, a, b, c)) :
    HasDerivAt (fun x => Φ (ε, a, x, c)) (partialB Φ (ε, a, b, c)) b :=
  hasDerivAt_partialSlot h ((hasDerivAt_const b ε).prodMk ((hasDerivAt_const b a).prodMk
    ((hasDerivAt_id b).prodMk (hasDerivAt_const b c)))) rfl

/-- The `c`-cofactor of `∂_b𝒯̂`: the cross density `b` reaches `𝒯̂` through the labellings
marking at least one vertex (whose weight carries `c`), through the `s^d` factor of the
single-marked-vertex labellings, and through the edge-density solve `Q`, whose
`b`-derivative is `-2c/(1-c)` (`hasDerivAt_Qmap_b`). -/
noncomputable def Rdb {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε a b c : ℝ) : ℝ :=
  (1 - c) ^ Fintype.card V
      * ((H.edgeFinset.card : ℝ) * Qmap ε a b c ^ (H.edgeFinset.card - 1) * (-2 / (1 - c)))
    + (Fintype.card V : ℝ) * (1 - c) ^ (Fintype.card V - 1)
        * ((d : ℝ) * b ^ (d - 1) * Qmap ε a b c ^ (H.edgeFinset.card - d)
          + b ^ d * (((H.edgeFinset.card - d : ℕ) : ℝ)
              * Qmap ε a b c ^ (H.edgeFinset.card - d - 1) * (-2 * c / (1 - c))))
    + c * partialB (ThatRem H) (ε, a, b, c)

/-- `Rdb` is jointly analytic away from `c = 1`. -/
theorem analyticAt_Rdb {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) {p : ℝ × ℝ × ℝ × ℝ} (hc : p.2.2.2 ≠ 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => Rdb H d w.1 w.2.1 w.2.2.1 w.2.2.2) p := by
  have hb := analyticAt_thd4 p
  have hcc := analyticAt_fth4 p
  have hQ := analyticAt_Qmap (p := p) hc
  have honec : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => 1 - w.2.2.2) p :=
    analyticAt_const.sub hcc
  have hden : ((1 : ℝ) - p.2.2.2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hinv0 : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => (-2 : ℝ) / (1 - w.2.2.2)) p :=
    analyticAt_const.div honec hden
  have hinv1 : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => -2 * w.2.2.2 / (1 - w.2.2.2)) p :=
    (analyticAt_const.mul hcc).div honec hden
  simp only [Rdb]
  refine AnalyticAt.add (AnalyticAt.add ?_ ?_)
    (hcc.mul (analyticAt_partialSlot _ (analyticAt_ThatRem H hc)))
  · exact (honec.pow _).mul ((analyticAt_const.mul (hQ.pow _)).mul hinv0)
  · exact (analyticAt_const.mul (honec.pow _)).mul
      (((analyticAt_const.mul (hb.pow _)).mul (hQ.pow _)).add
        ((hb.pow _).mul ((analyticAt_const.mul (hQ.pow _)).mul hinv1)))

/-- **`∂_b𝒯̂` is exactly `c` times an analytic function.**  The companion of
`hasDerivAt_That_a` of `KRRS/TCalc.lean` in the `b`-direction: paragraph 3 of Appendix A
divides the `b`-stationarity equation by one power of `c`. -/
theorem hasDerivAt_That_b {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {ε a b c : ℝ} (hc : c ≠ 1) :
    HasDerivAt (fun x => That H ε a x c) (c * Rdb H d ε a b c) b := by
  have hc' : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hQb : HasDerivAt (fun x : ℝ => Qmap ε a x c) (-2 * c / (1 - c)) b :=
    hasDerivAt_Qmap_b hc ε a b
  have hQpow : ∀ k : ℕ, HasDerivAt (fun x : ℝ => Qmap ε a x c ^ k)
      ((k : ℝ) * Qmap ε a b c ^ (k - 1) * (-2 * c / (1 - c))) b := fun k => hQb.fun_pow k
  have hT1 : HasDerivAt
      (fun x : ℝ => (1 - c) ^ Fintype.card V * Qmap ε a x c ^ H.edgeFinset.card)
      ((1 - c) ^ Fintype.card V * ((H.edgeFinset.card : ℝ)
        * Qmap ε a b c ^ (H.edgeFinset.card - 1) * (-2 * c / (1 - c)))) b :=
    (hQpow H.edgeFinset.card).const_mul _
  have hT2 : HasDerivAt
      (fun x : ℝ => (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
        * (x ^ d * Qmap ε a x c ^ (H.edgeFinset.card - d)))
      ((Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
        * ((d : ℝ) * b ^ (d - 1) * Qmap ε a b c ^ (H.edgeFinset.card - d)
          + b ^ d * (((H.edgeFinset.card - d : ℕ) : ℝ)
              * Qmap ε a b c ^ (H.edgeFinset.card - d - 1) * (-2 * c / (1 - c))))) b :=
    ((hasDerivAt_pow d b).mul (hQpow (H.edgeFinset.card - d))).const_mul _
  have hT3 : HasDerivAt (fun x : ℝ => c ^ 2 * tBipRem2 H a x (Qmap ε a x c) c)
      (c ^ 2 * partialB (ThatRem H) (ε, a, b, c)) b :=
    (hasDerivAt_partialB (Φ := ThatRem H) (analyticAt_ThatRem H hc)).const_mul (c ^ 2)
  have hfun : (fun x => That H ε a x c) = fun x : ℝ =>
      (1 - c) ^ Fintype.card V * Qmap ε a x c ^ H.edgeFinset.card
        + (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
            * (x ^ d * Qmap ε a x c ^ (H.edgeFinset.card - d))
        + c ^ 2 * tBipRem2 H a x (Qmap ε a x c) c := by
    funext x
    exact tBip_factored H hreg a x (Qmap ε a x c) c
  rw [hfun]
  have h := (hT1.add hT2).add hT3
  convert h using 1
  all_goals try rfl
  simp only [Rdb]
  field_simp

end UpperTailOptimizers
