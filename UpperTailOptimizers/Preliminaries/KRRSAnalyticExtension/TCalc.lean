import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Reduced

/-!
# The `H`-density half of Appendix B, paragraph 2

Paragraph 2 of Appendix B of `paper/paper.tex` expands the
homomorphism-density sum according to the set of vertices assigned to the first pode and
reads off the first `c`-derivative of the edge-constrained `H`-density `𝒯̂`.  This file
carries out that computation.

Throughout, `H` is `d`-regular, so the paper's vertex counts degenerate to `n₁ = 0`,
`n_d = v = |V(H)|`; we write `n := |V(H)|` and `m := |E(H)|`.

## Contents

* `tBipRem2`, `tBipRem_eq_sq_mul` — the small-block remainder of
  `NonexceptionalEndpoint/QuadraticGrowth/TDensityExpansion.lean` carries a factor `c²` *exactly*: every surviving
  labelling marks at least two vertices.  That the cofactor `tBipRem2` is a polynomial in
  the four block parameters is recorded by a file-private analyticity lemma.
* `tBip_factored` — the resulting exact factored form of the labelling polynomial,
  `tBip = (1-c)ⁿ qᵐ + n c (1-c)^{n-1} s^d q^{m-d} + c² · tBipRem2`.
* `Afun` — the paper's `𝒜(ε,b) = n_d ε^{m-d} 𝒟_ε(b)` `eq:krrs-density-coefficient`.
* `hasDerivAt_That_c_zero` — **`eq:krrs-density-derivative`**: `∂_c𝒯̂|_{c=0} = 𝒜(ε,b)`.
  The three summands of `tBip_factored` contribute `-nεᵐ + 2mε^{m-1}(ε-b)`,
  `n b^d ε^{m-d}` and `0`; the handshake identity `n d = 2m` turns the total into
  `n ε^{m-d} 𝒟_ε(b)`.
* `analyticAt_That` — joint real-analyticity of `𝒯̂` away from `c = 1`, the input to the
  analytic implicit function theorem of `eq:krrs-density-constraint`.
* `partialSlot`, `analyticAt_partialSlot`, `hasDerivAt_partialSlot` — the directional
  derivative of a function of `(ε,a,b,c)` in a fixed direction `e`, taken as a Fréchet slot
  so that it is visibly analytic.  Specialising `e` to a basis vector gives `partialA`
  here, `partialB` (`Preliminaries/KRRSAnalyticExtension/TCalcAB.lean`) and `partialC` (`Preliminaries/KRRSAnalyticExtension/Stationarity.lean`).
* `partialA`, `Rda`, `hasDerivAt_That_a` — the companion `a`-side bookkeeping: `a` reaches
  `𝒯̂` only through `Q` (with `∂_aQ = -c²/(1-c)²`) and through the `≥ 2`-marked
  labellings, so `∂_a𝒯̂ = c²·Rda` with `Rda` jointly analytic on `{c ≠ 1}`.
-/

namespace UpperTailOptimizers

open Real Filter Topology

/-! ### Exact `c²` divisibility of the small-block remainder -/

/-- `tBipRem` divided by `c²`: every surviving labelling has at least two marked
vertices, so the weight carries a factor `c²` exactly. -/
noncomputable def tBipRem2 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q c : ℝ) : ℝ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ),
    edgeProd H a s q τ * (c ^ (trueCount τ - 2) * (1 - c) ^ (Fintype.card V - trueCount τ))

/-- **The remainder of the small-block expansion is exactly `c²` times a polynomial.**
Pointwise `c^{k(τ)} = c² · c^{k(τ)-2}` on the index set, where `k(τ) ≥ 2`. -/
theorem tBipRem_eq_sq_mul {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q c : ℝ) :
    tBipRem H a s q c = c ^ 2 * tBipRem2 H a s q c := by
  classical
  simp only [tBipRem, tBipRem2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  have h2 : 2 ≤ trueCount τ := (Finset.mem_filter.mp hτ).2
  have hpow : c ^ trueCount τ = c ^ 2 * c ^ (trueCount τ - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  ring

/-- The `c²`-cofactor of the remainder is a polynomial in the four block parameters, hence
jointly real-analytic (mirrors `analyticAt_bipTd` of `Preliminaries/KRRSAnalyticExtension/Chart.lean`). -/
private theorem analyticAt_tBipRem2 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p : ℝ × ℝ × ℝ × ℝ) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => tBipRem2 H w.1 w.2.1 w.2.2.1 w.2.2.2) p := by
  classical
  simp only [tBipRem2, edgeProd]
  refine Finset.analyticAt_fun_sum _ (fun τ _ => AnalyticAt.mul ?_ ?_)
  · refine Finset.analyticAt_fun_prod _ (fun e _ => ?_)
    induction e using Sym2.ind with
    | _ x y =>
      show AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => blockVal w.1 w.2.1 w.2.2.1 (τ x) (τ y)) p
      cases τ x <;> cases τ y <;>
        first
          | exact analyticAt_fst4 p
          | exact analyticAt_snd4 p
          | exact analyticAt_thd4 p
  · exact ((analyticAt_fth4 p).pow _).mul ((analyticAt_const.sub (analyticAt_fth4 p)).pow _)

/-- **The exact factored form of `tBip`** for a `d`-regular `H`: the small-block expansion
of `NonexceptionalEndpoint/QuadraticGrowth/TDensityExpansion.lean` with its remainder written as `c²` times a
polynomial. -/
theorem tBip_factored {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) (a s q c : ℝ) :
    tBip H a s q c = (1 - c) ^ (Fintype.card V) * q ^ H.edgeFinset.card
      + (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
          * (s ^ d * q ^ (H.edgeFinset.card - d))
      + c ^ 2 * tBipRem2 H a s q c := by
  rw [tBip_expansion H hreg a s q c, tBipRem_eq_sq_mul]

/-! ### The first `c`-derivative of `𝒯̂` -/

/-- The paper's `𝒜(ε,b) = n_d ε^{m-d} 𝒟_ε(b)` `eq:krrs-density-coefficient`.  Here every vertex
of `H` has degree `d`, so `n_d = |V|`. -/
noncomputable def Afun {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε b : ℝ) : ℝ :=
  (Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * Dfun d ε b

/-- `𝒜(ε,b) > 0` for `0 ≤ b ≠ ε`, the paper's "in particular `𝒜(ε₀,z₀) > 0`".  This is the
nonvanishing that drives both implicit function theorem steps of Appendix B: it is the
`c`-slot of the Jacobian in paragraph 2, and it enters the entry `S₀''(a₀)/𝒜(ε₀,z₀)²` of
`eq:krrs-jacobian-aa` in paragraph 3 (a factor multiplying `S₀''(a)` in the normalisation of
`Preliminaries/KRRSAnalyticExtension/Stationarity.lean`).  Strict convexity of `z ↦ z^d` gives `𝒟_ε(b) > 0` (`Dfun_pos`), and
a graph with an edge has a vertex (`nonempty_of_edge`), so `n_d = |V| > 0`. -/
theorem Afun_pos {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ H.edgeFinset.card)
    {ε b : ℝ} (hε : 0 < ε) (hb0 : 0 ≤ b) (hb : b ≠ ε) :
    0 < Afun H d ε b := by
  have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr (nonempty_of_edge H hm)
  have hVR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hpow : (0 : ℝ) < ε ^ (H.edgeFinset.card - d) := pow_pos hε _
  unfold Afun
  exact mul_pos (mul_pos hVR hpow) (Dfun_pos hd hε hb0 hb)

/-- **`eq:krrs-density-derivative`**: `∂_c 𝒯̂|_{c=0} = 𝒜(ε,b)`.

The all-second-pode labelling contributes `-n εᵐ` from the block-mass factor and
`2m ε^{m-1}(ε-b)` from the `m` factors of `Q` (using `∂_cQ|_{c=0} = 2(ε-b)`); the
single-marked-vertex labellings contribute `n b^d ε^{m-d}`; the rest is `O(c²)`.  The
handshake identity `n d = 2m` collapses the total to `n ε^{m-d} 𝒟_ε(b)`. -/
theorem hasDerivAt_That_c_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) (ε a b : ℝ) :
    HasDerivAt (fun c => That H ε a b c) (Afun H d ε b) 0 := by
  classical
  -- `d ≤ m`, so the natural-number subtractions `m - d`, `m - 1` below behave.
  have hdm : d ≤ H.edgeFinset.card := degree_le_card_edges H hreg (by omega)
  -- the `c`-behaviour of the edge-density solve `Q`
  have hQ0 : Qmap ε a b 0 = ε := Qmap_zero ε a b
  have hQd : HasDerivAt (fun c => Qmap ε a b c) (2 * (ε - b)) 0 := hasDerivAt_Qmap_c ε a b
  have hQpow : ∀ k : ℕ, HasDerivAt (fun c : ℝ => Qmap ε a b c ^ k)
      ((k : ℝ) * ε ^ (k - 1) * (2 * (ε - b))) 0 := by
    intro k
    have h := hQd.fun_pow k
    rwa [hQ0] at h
  have hone : HasDerivAt (fun c : ℝ => (1 : ℝ) - c) (-1) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub (hasDerivAt_id (0 : ℝ))
  -- summand 1: the all-second-pode labelling
  have h1c : HasDerivAt (fun c : ℝ => (1 - c) ^ Fintype.card V)
      (-(Fintype.card V : ℝ)) 0 := by
    have h := hone.fun_pow (Fintype.card V)
    simpa using h
  have hT1 : HasDerivAt
      (fun c : ℝ => (1 - c) ^ Fintype.card V * Qmap ε a b c ^ H.edgeFinset.card)
      (-(Fintype.card V : ℝ) * ε ^ H.edgeFinset.card
        + (H.edgeFinset.card : ℝ) * ε ^ (H.edgeFinset.card - 1) * (2 * (ε - b))) 0 := by
    have h := h1c.fun_mul (hQpow H.edgeFinset.card)
    convert h using 1
    all_goals try rfl
    rw [hQ0]
    norm_num
  -- summand 2: the labellings marking exactly one vertex
  have hg : HasDerivAt
      (fun c : ℝ => (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1))
      (Fintype.card V : ℝ) 0 := by
    have hlin : HasDerivAt (fun c : ℝ => (Fintype.card V : ℝ) * c)
        (Fintype.card V : ℝ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul ((Fintype.card V : ℝ))
    have h := hlin.fun_mul (hone.fun_pow (Fintype.card V - 1))
    convert h using 1
    all_goals try rfl
    norm_num
  have hh : HasDerivAt
      (fun c : ℝ => b ^ d * Qmap ε a b c ^ (H.edgeFinset.card - d))
      (b ^ d * (((H.edgeFinset.card - d : ℕ) : ℝ) * ε ^ (H.edgeFinset.card - d - 1)
        * (2 * (ε - b)))) 0 :=
    (hQpow (H.edgeFinset.card - d)).const_mul (b ^ d)
  have hT2 : HasDerivAt
      (fun c : ℝ => (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
        * (b ^ d * Qmap ε a b c ^ (H.edgeFinset.card - d)))
      ((Fintype.card V : ℝ) * (b ^ d * ε ^ (H.edgeFinset.card - d))) 0 := by
    have h := hg.fun_mul hh
    convert h using 1
    all_goals try rfl
    rw [hQ0]
    norm_num
  -- summand 3: the `O(c²)` remainder
  have hQan : AnalyticAt ℝ (fun c : ℝ => Qmap ε a b c) 0 := by
    have h := analyticAt_Qmap (p := ((ε, a, b, (0 : ℝ)) : ℝ × ℝ × ℝ × ℝ)) (by norm_num)
    have hpt : AnalyticAt ℝ (fun c : ℝ => ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ)) 0 :=
      analyticAt_const.prod (analyticAt_const.prod (analyticAt_const.prod analyticAt_id))
    exact AnalyticAt.fun_comp (f := fun c : ℝ => ((ε, a, b, c) : ℝ × ℝ × ℝ × ℝ)) h hpt
  have hRdiff : DifferentiableAt ℝ (fun c : ℝ => tBipRem2 H a b (Qmap ε a b c) c) 0 := by
    have hpath : AnalyticAt ℝ
        (fun c : ℝ => ((a, b, Qmap ε a b c, c) : ℝ × ℝ × ℝ × ℝ)) 0 :=
      analyticAt_const.prod (analyticAt_const.prod (hQan.prod analyticAt_id))
    exact ((analyticAt_tBipRem2 H _).fun_comp hpath).differentiableAt
  have hsq : HasDerivAt (fun c : ℝ => c ^ 2) (0 : ℝ) 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have hT3 : HasDerivAt
      (fun c : ℝ => c ^ 2 * tBipRem2 H a b (Qmap ε a b c) c) 0 0 := by
    have h := hsq.fun_mul hRdiff.hasDerivAt
    convert h using 1
    all_goals try rfl
    norm_num
  -- assemble
  have hfun : (fun c => That H ε a b c) = fun c : ℝ =>
      (1 - c) ^ Fintype.card V * Qmap ε a b c ^ H.edgeFinset.card
        + (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
            * (b ^ d * Qmap ε a b c ^ (H.edgeFinset.card - d))
        + c ^ 2 * tBipRem2 H a b (Qmap ε a b c) c := by
    funext c
    exact tBip_factored H hreg a b (Qmap ε a b c) c
  rw [hfun]
  have h := (hT1.add hT2).add hT3
  convert h using 1
  all_goals try rfl
  -- the exponent bookkeeping and the handshake identity
  have e1 : ε ^ (H.edgeFinset.card - d) * ε ^ d = ε ^ H.edgeFinset.card := by
    rw [← pow_add]
    congr 1
    omega
  have e2 : ε ^ (H.edgeFinset.card - d) * ε ^ (d - 1) = ε ^ (H.edgeFinset.card - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hnd : (Fintype.card V : ℝ) * (d : ℝ) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast regular_handshake H hreg
  unfold Afun Dfun
  have expand : (Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d)
      * (b ^ d - ε ^ d - (d : ℝ) * ε ^ (d - 1) * (b - ε))
      = (Fintype.card V : ℝ) * (b ^ d * ε ^ (H.edgeFinset.card - d))
        - (Fintype.card V : ℝ) * (ε ^ (H.edgeFinset.card - d) * ε ^ d)
        - ((Fintype.card V : ℝ) * (d : ℝ))
            * (ε ^ (H.edgeFinset.card - d) * ε ^ (d - 1)) * (b - ε) := by
    ring
  rw [expand, e1, e2, hnd]
  ring

/-! ### Joint analyticity of `𝒯̂` -/

/-- **`𝒯̂` is jointly real-analytic in `(ε,a,b,c)` away from `c = 1`.**  This is the
regularity hypothesis of the analytic implicit function theorem invoked at
`eq:krrs-density-constraint`. -/
theorem analyticAt_That {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {p : ℝ × ℝ × ℝ × ℝ} (hc : p.2.2.2 ≠ 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) p := by
  have ha := analyticAt_snd4 p
  have hb := analyticAt_thd4 p
  have hcc := analyticAt_fth4 p
  have hQ := analyticAt_Qmap (p := p) hc
  exact (analyticAt_bipTd H _).fun_comp (ha.prod (hb.prod (hQ.prod hcc)))

/-! ### Directional derivatives in the four appendix parameters -/

/-- The derivative of a function of the four appendix parameters `(ε,a,b,c)` in the fixed
direction `e`, packaged as a function of the same four parameters.  Using the Fréchet
derivative rather than a hand-written formula keeps it manifestly analytic
(`analyticAt_partialSlot`) while still computing the ordinary directional derivative
(`hasDerivAt_partialSlot`).  Taking `e` to be a basis vector gives the coordinate partials
`partialA` (below), `partialB` (`Preliminaries/KRRSAnalyticExtension/TCalcAB.lean`) and `partialC`
(`Preliminaries/KRRSAnalyticExtension/Stationarity.lean`). -/
noncomputable def partialSlot (e : ℝ × ℝ × ℝ × ℝ) (Φ : ℝ × ℝ × ℝ × ℝ → ℝ)
    (w : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  fderiv ℝ Φ w e

/-- A directional derivative of an analytic function is analytic. -/
theorem analyticAt_partialSlot (e : ℝ × ℝ × ℝ × ℝ) {Φ : ℝ × ℝ × ℝ × ℝ → ℝ}
    {p : ℝ × ℝ × ℝ × ℝ} (h : AnalyticAt ℝ Φ p) : AnalyticAt ℝ (partialSlot e Φ) p :=
  ((ContinuousLinearMap.apply ℝ ℝ e).analyticAt (fderiv ℝ Φ p)).fun_comp h.fderiv

/-- **`partialSlot e Φ w` really is the derivative along any curve with velocity `e`.**
If `γ` passes through `w` at time `x` with `γ' x = e`, then `t ↦ Φ (γ t)` has derivative
`partialSlot e Φ w` at `x`.  The coordinate partials use straight lines for `γ`;
`Preliminaries/KRRSAnalyticExtension/SigmaLink.lean` uses the graph of the chart `C`. -/
theorem hasDerivAt_partialSlot {e : ℝ × ℝ × ℝ × ℝ} {Φ : ℝ × ℝ × ℝ × ℝ → ℝ}
    {w : ℝ × ℝ × ℝ × ℝ} (h : AnalyticAt ℝ Φ w) {γ : ℝ → ℝ × ℝ × ℝ × ℝ} {x : ℝ}
    (hγ : HasDerivAt γ e x) (hγx : γ x = w) :
    HasDerivAt (fun t => Φ (γ t)) (partialSlot e Φ w) x := by
  subst hγx
  exact h.differentiableAt.hasFDerivAt.comp_hasDerivAt x hγ

/-! ### The `a`-derivative of `𝒯̂` is exactly `c²` times an analytic function -/

/-- The partial derivative in the second slot `a` of a function of the four appendix
parameters `(ε,a,b,c)`. -/
noncomputable abbrev partialA (Φ : ℝ × ℝ × ℝ × ℝ → ℝ) (w : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  partialSlot (0, 1, 0, 0) Φ w

/-- The `a`-partial really is the derivative of `x ↦ Φ(ε,x,b,c)`. -/
theorem hasDerivAt_partialA {Φ : ℝ × ℝ × ℝ × ℝ → ℝ} {ε a b c : ℝ}
    (h : AnalyticAt ℝ Φ (ε, a, b, c)) :
    HasDerivAt (fun x => Φ (ε, x, b, c)) (partialA Φ (ε, a, b, c)) a :=
  hasDerivAt_partialSlot h ((hasDerivAt_const a ε).prodMk ((hasDerivAt_id a).prodMk
    ((hasDerivAt_const a b).prodMk (hasDerivAt_const a c)))) rfl

/-- The `O(c²)` part of `𝒯̂`, as a function of the four appendix parameters: the only
place where the first-pode density `a` enters the factored form `tBip_factored`. -/
noncomputable def ThatRem {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (w : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  tBipRem2 H w.2.1 w.2.2.1 (Qmap w.1 w.2.1 w.2.2.1 w.2.2.2) w.2.2.2

/-- `ThatRem` is jointly analytic away from `c = 1`. -/
theorem analyticAt_ThatRem {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {p : ℝ × ℝ × ℝ × ℝ} (hc : p.2.2.2 ≠ 1) :
    AnalyticAt ℝ (ThatRem H) p := by
  have ha := analyticAt_snd4 p
  have hb := analyticAt_thd4 p
  have hcc := analyticAt_fth4 p
  have hQ := analyticAt_Qmap (p := p) hc
  exact (analyticAt_tBipRem2 H _).fun_comp (ha.prod (hb.prod (hQ.prod hcc)))

/-- The `c²`-cofactor of `∂_a𝒯̂`: the first-pode density `a` reaches `𝒯̂` only through the
edge-density solve `Q` (whose `a`-derivative is `-c²/(1-c)²`) and through the labellings
with at least two marked vertices (which carry `c²` by `tBipRem_eq_sq_mul`). -/
noncomputable def Rda {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε a b c : ℝ) : ℝ :=
  (1 - c) ^ Fintype.card V
      * ((H.edgeFinset.card : ℝ) * Qmap ε a b c ^ (H.edgeFinset.card - 1)
          * (-1 / (1 - c) ^ 2))
    + (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
        * (b ^ d * (((H.edgeFinset.card - d : ℕ) : ℝ)
            * Qmap ε a b c ^ (H.edgeFinset.card - d - 1) * (-1 / (1 - c) ^ 2)))
    + partialA (ThatRem H) (ε, a, b, c)

/-- `Rda` is jointly analytic away from `c = 1`. -/
theorem analyticAt_Rda {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) {p : ℝ × ℝ × ℝ × ℝ} (hc : p.2.2.2 ≠ 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => Rda H d w.1 w.2.1 w.2.2.1 w.2.2.2) p := by
  have hb := analyticAt_thd4 p
  have hcc := analyticAt_fth4 p
  have hQ := analyticAt_Qmap (p := p) hc
  have honec : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => 1 - w.2.2.2) p :=
    analyticAt_const.sub hcc
  have hden : ((1 : ℝ) - p.2.2.2) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hc))
  have hinv : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => -1 / (1 - w.2.2.2) ^ 2) p :=
    analyticAt_const.div (honec.pow 2) hden
  simp only [Rda]
  refine AnalyticAt.add (AnalyticAt.add ?_ ?_)
    (analyticAt_partialSlot _ (analyticAt_ThatRem H hc))
  · exact (honec.pow _).mul ((analyticAt_const.mul (hQ.pow _)).mul hinv)
  · exact ((analyticAt_const.mul hcc).mul (honec.pow _)).mul
      ((hb.pow d).mul ((analyticAt_const.mul (hQ.pow _)).mul hinv))

/-- **`∂_a𝒯̂` is exactly `c²` times an analytic function.**  This is the nondegeneracy
bookkeeping of paragraph 3: the `a`-direction is invisible at `c = 0` to second order. -/
theorem hasDerivAt_That_a {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {ε a b c : ℝ} (hc : c ≠ 1) :
    HasDerivAt (fun x => That H ε x b c) (c ^ 2 * Rda H d ε a b c) a := by
  have hQa : HasDerivAt (fun x : ℝ => Qmap ε x b c) (-(c ^ 2) / (1 - c) ^ 2) a := by
    have h1 : HasDerivAt (fun x : ℝ => c ^ 2 * x) (c ^ 2) a := by
      simpa using (hasDerivAt_id a).const_mul (c ^ 2)
    have hnum : HasDerivAt (fun x : ℝ => ε - c ^ 2 * x - 2 * c * (1 - c) * b) (-(c ^ 2)) a := by
      simpa using ((hasDerivAt_const a ε).sub h1).sub_const (2 * c * (1 - c) * b)
    exact hnum.div_const ((1 - c) ^ 2)
  have hQpow : ∀ k : ℕ, HasDerivAt (fun x : ℝ => Qmap ε x b c ^ k)
      ((k : ℝ) * Qmap ε a b c ^ (k - 1) * (-(c ^ 2) / (1 - c) ^ 2)) a := fun k => hQa.fun_pow k
  have hT1 : HasDerivAt
      (fun x : ℝ => (1 - c) ^ Fintype.card V * Qmap ε x b c ^ H.edgeFinset.card)
      ((1 - c) ^ Fintype.card V * ((H.edgeFinset.card : ℝ)
        * Qmap ε a b c ^ (H.edgeFinset.card - 1) * (-(c ^ 2) / (1 - c) ^ 2))) a :=
    (hQpow H.edgeFinset.card).const_mul _
  have hT2 : HasDerivAt
      (fun x : ℝ => (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
        * (b ^ d * Qmap ε x b c ^ (H.edgeFinset.card - d)))
      ((Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
        * (b ^ d * (((H.edgeFinset.card - d : ℕ) : ℝ)
            * Qmap ε a b c ^ (H.edgeFinset.card - d - 1)
            * (-(c ^ 2) / (1 - c) ^ 2)))) a :=
    ((hQpow (H.edgeFinset.card - d)).const_mul (b ^ d)).const_mul _
  have hT3 : HasDerivAt (fun x : ℝ => c ^ 2 * tBipRem2 H x b (Qmap ε x b c) c)
      (c ^ 2 * partialA (ThatRem H) (ε, a, b, c)) a :=
    (hasDerivAt_partialA (Φ := ThatRem H) (analyticAt_ThatRem H hc)).const_mul (c ^ 2)
  have hfun : (fun x => That H ε x b c) = fun x : ℝ =>
      (1 - c) ^ Fintype.card V * Qmap ε x b c ^ H.edgeFinset.card
        + (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
            * (b ^ d * Qmap ε x b c ^ (H.edgeFinset.card - d))
        + c ^ 2 * tBipRem2 H x b (Qmap ε x b c) c := by
    funext x
    exact tBip_factored H hreg x b (Qmap ε x b c) c
  rw [hfun]
  have h := (hT1.add hT2).add hT3
  convert h using 1
  all_goals try rfl
  simp only [Rda]
  ring

end UpperTailOptimizers
