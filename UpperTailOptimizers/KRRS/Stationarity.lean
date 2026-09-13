import UpperTailOptimizers.KRRS.TCalcAB
import UpperTailOptimizers.KRRS.PsiNondeg

/-!
# The desingularized stationarity equations of Appendix A, paragraph 3

Paragraph 3 of Appendix A of `paper/bipodal_optimizer.tex` (Appendix A) divides the two
stationarity equations of the reduced entropy by the powers of the pode size `c` that make
them extend analytically across the degenerate boundary `c = 0`, and then evaluates the
resulting system and its `(a,b)`-Jacobian there.

The quotients the paper writes as limits are available here *exactly*, because
`KRRS/SCalc.lean` and `KRRS/TCalcAB.lean` compute the four partial derivatives in already
factored form:

`∂_aŜ = c²(S₀'(a) - S₀'(Q))`,  `∂_bŜ = 2c(1-c)(S₀'(b) - S₀'(Q))`,
`∂_a𝒯̂ = c²·Rda`,               `∂_b𝒯̂ = c·Rdb`.

So `F1` and `F2` below are defined with no division at all; they are `c²`, resp. `c`, times
the naive Wronskian-style stationarity expressions.

## Contents

* `partialC` — the `c`-partial in the style of `partialA` (`KRRS/TCalc.lean`) and
  `partialB` (`KRRS/TCalcAB.lean`), together with its two boundary values
  `partialC_That_zero` (`= 𝒜(ε,b)`, `eq:krrs-density-derivative`) and `partialC_Shat_zero`
  (`= 𝒩_ε(b)`, `eq:krrs-entropy-derivative`), and the neighbourhood form
  `eventually_partialC_That_ne_zero` of the first.  The analyticity and derivative rules
  for `partialC` itself are file-private.
* `F1`, `F2` — the desingularized system, the analytic incarnations of
  `eq:krrs-small-block-stationarity` and `eq:krrs-cross-block-stationarity`.
* `analyticAt_F1`, `analyticAt_F2` — joint real-analyticity in `(ε,a,b,c)`, the regularity
  input of the analytic implicit function theorem of `eq:krrs-stationary-densities`.
* `Rdb_zero`, `F2_zero_eq` — **the critical evaluation**:
  `F₂|_{c=0} = n ε^{m-d} · Wr_d(ε,b)`, the quotient-free form of
  `eq:krrs-quotient-boundary`.
* `hasDerivAt_F1_a_zero` `eq:krrs-jacobian-aa`, `hasDerivAt_F2_a_zero` `eq:krrs-jacobian-ba`,
  `hasDerivAt_F2_b_zero` `eq:krrs-jacobian-bb` — the three Jacobian entries at `c = 0`.
* `F_jacobian_nondegenerate` — the payoff: at the KRR–S base point the `(a,b)`-Jacobian of
  `(F₁,F₂)` at `ϑ = 0` is triangular with nonzero diagonal, and `F₂` vanishes there.

Throughout, `n := |V(H)|` and `m := |E(H)|`, and `H` is `d`-regular with `d ≥ 2`.
-/

namespace UpperTailOptimizers

open Real Filter Topology

/-! ### The `c`-partial -/

/-- The partial derivative in the fourth slot `c` of a function of the four appendix
parameters `(ε,a,b,c)` — the `c`-analogue of `partialA` (`KRRS/TCalc.lean`) and `partialB`
(`KRRS/TCalcAB.lean`). -/
noncomputable abbrev partialC (Φ : ℝ × ℝ × ℝ × ℝ → ℝ) (w : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  partialSlot (0, 0, 0, 1) Φ w

/-- The `c`-partial of an analytic function is analytic. -/
private theorem analyticAt_partialC {Φ : ℝ × ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ × ℝ}
    (h : AnalyticAt ℝ Φ p) : AnalyticAt ℝ (partialC Φ) p :=
  analyticAt_partialSlot _ h

/-- The `c`-partial really is the derivative of `x ↦ Φ(ε,a,b,x)`. -/
private theorem hasDerivAt_partialC {Φ : ℝ × ℝ × ℝ × ℝ → ℝ} {ε a b c : ℝ}
    (h : AnalyticAt ℝ Φ (ε, a, b, c)) :
    HasDerivAt (fun x => Φ (ε, a, b, x)) (partialC Φ (ε, a, b, c)) c :=
  hasDerivAt_partialSlot h ((hasDerivAt_const c ε).prodMk ((hasDerivAt_const c a).prodMk
    ((hasDerivAt_const c b).prodMk (hasDerivAt_id c)))) rfl

/-- **`eq:krrs-density-derivative` in `partialC` form**: `∂_c𝒯̂|_{c=0} = 𝒜(ε,b)`.  The
Fréchet `c`-slot of `𝒯̂` and the honest `c`-derivative `hasDerivAt_That_c_zero` agree by
uniqueness of the derivative. -/
theorem partialC_That_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) (ε a b : ℝ) :
    partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, 0)
      = Afun H d ε b := by
  have h1 : HasDerivAt (fun c => That H ε a b c)
      (partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, 0))
      (0 : ℝ) :=
    hasDerivAt_partialC (Φ := fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2)
      (analyticAt_That H (p := ((ε, a, b, (0 : ℝ)) : ℝ × ℝ × ℝ × ℝ)) (by norm_num))
  exact h1.unique (hasDerivAt_That_c_zero H hd hreg hm ε a b)

/-- **`∂_c𝒯̂ ≠ 0` on a whole neighbourhood of the degenerate base point.**  At `c = 0` the
`c`-partial of `𝒯̂` is `𝒜(ε,b)` (`partialC_That_zero`), which is strictly positive for
`0 ≤ b ≠ ε` (`Afun_pos`); and `partialC 𝒯̂` is continuous, being analytic
(`analyticAt_partialC` applied to `analyticAt_That`).

This is the nondegeneracy that `Bipodality/Optimal.lean` feeds to `F_eq_zero_of_maximizer`
(`KRRS/MaximizerStationary.lean`). -/
theorem eventually_partialC_That_ne_zero {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card) {ε b : ℝ} (a : ℝ)
    (hε : 0 < ε) (hb0 : 0 ≤ b) (hbε : b ≠ ε) :
    ∀ᶠ w in 𝓝 ((ε, a, b, 0) : ℝ × ℝ × ℝ × ℝ),
      partialC (fun v : ℝ × ℝ × ℝ × ℝ => That H v.1 v.2.1 v.2.2.1 v.2.2.2) w ≠ 0 := by
  have hcont : ContinuousAt
      (partialC (fun v : ℝ × ℝ × ℝ × ℝ => That H v.1 v.2.1 v.2.2.1 v.2.2.2))
      ((ε, a, b, 0) : ℝ × ℝ × ℝ × ℝ) :=
    (analyticAt_partialC (analyticAt_That H
      (p := ((ε, a, b, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ)) (by norm_num))).continuousAt
  refine hcont.eventually_ne ?_
  rw [partialC_That_zero H hd hreg hm ε a b]
  exact ne_of_gt (Afun_pos H hd (by omega) hε hb0 hbε)

/-- **`eq:krrs-entropy-derivative` in `partialC` form**: `∂_cŜ|_{c=0} = 𝒩_ε(b)`. -/
theorem partialC_Shat_zero {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    partialC (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, 0)
      = Nfun ε b := by
  have hS : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε, a, b, (0 : ℝ)) : ℝ × ℝ × ℝ × ℝ) := by
    refine analyticAt_Shat (p := ((ε, a, b, (0 : ℝ)) : ℝ × ℝ × ℝ × ℝ)) (by norm_num)
      ha0 ha1 hb0 hb1 ?_ ?_
    · simpa using hε0
    · simpa using hε1
  have h1 : HasDerivAt (fun c => Shat ε a b c)
      (partialC (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, 0))
      (0 : ℝ) :=
    hasDerivAt_partialC (Φ := fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2) hS
  exact h1.unique (hasDerivAt_Shat_c_zero hε0 hε1 a b)

/-! ### The two desingularized stationarity functions -/

/-- **`eq:krrs-small-block-stationarity`**, in desingularized form:
`F₁ = (∂_aŜ/c²)·∂_c𝒯̂ - ∂_cŜ·(∂_a𝒯̂/c²)`.

Both quotients are available exactly: `∂_aŜ = c²(S₀'(a) - S₀'(Q))` by
`hasDerivAt_Shat_a` and `∂_a𝒯̂ = c²·Rda` by `hasDerivAt_That_a`, so no division occurs. -/
noncomputable def F1 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε a b c : ℝ) : ℝ :=
  (dS0 a - dS0 (Qmap ε a b c))
      * partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
    - partialC (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
        * Rda H d ε a b c

/-- **`eq:krrs-cross-block-stationarity`**, in desingularized form:
`F₂ = (∂_bŜ/c)·∂_c𝒯̂ - ∂_cŜ·(∂_b𝒯̂/c)`.

Again the quotients are exact: `∂_bŜ = 2c(1-c)(S₀'(b) - S₀'(Q))` by `hasDerivAt_Shat_b`
and `∂_b𝒯̂ = c·Rdb` by `hasDerivAt_That_b`. -/
noncomputable def F2 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε a b c : ℝ) : ℝ :=
  (2 * (1 - c) * (dS0 b - dS0 (Qmap ε a b c)))
      * partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
    - partialC (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2) (ε, a, b, c)
        * Rdb H d ε a b c

/-! ### Joint analyticity -/

/-- **`F₁` is jointly real-analytic in `(ε,a,b,c)`** away from `c = 1` and at points where
the three block densities `a`, `b`, `Q(ε,a,b,c)` lie in `(0,1)`.  This is the regularity
hypothesis of the analytic implicit function theorem invoked at `eq:krrs-stationary-densities`. -/
theorem analyticAt_F1 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) {p : ℝ × ℝ × ℝ × ℝ} (hc : p.2.2.2 ≠ 1)
    (ha0 : 0 < p.2.1) (ha1 : p.2.1 < 1) (hb0 : 0 < p.2.2.1) (hb1 : p.2.2.1 < 1)
    (hQ0 : 0 < Qmap p.1 p.2.1 p.2.2.1 p.2.2.2) (hQ1 : Qmap p.1 p.2.1 p.2.2.1 p.2.2.2 < 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => F1 H d w.1 w.2.1 w.2.2.1 w.2.2.2) p := by
  have hpa := analyticAt_snd4 p
  have hda : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => dS0 w.2.1) p :=
    AnalyticAt.fun_comp (g := dS0) (f := fun w : ℝ × ℝ × ℝ × ℝ => w.2.1)
      (analyticAt_dS0 ha0 ha1) hpa
  have hdQ : AnalyticAt ℝ
      (fun w : ℝ × ℝ × ℝ × ℝ => dS0 (Qmap w.1 w.2.1 w.2.2.1 w.2.2.2)) p :=
    AnalyticAt.fun_comp (g := dS0)
      (f := fun w : ℝ × ℝ × ℝ × ℝ => Qmap w.1 w.2.1 w.2.2.1 w.2.2.2)
      (analyticAt_dS0 hQ0 hQ1) (analyticAt_Qmap hc)
  have hT : AnalyticAt ℝ
      (partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2)) p :=
    analyticAt_partialC (analyticAt_That H hc)
  have hS : AnalyticAt ℝ
      (partialC (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2)) p := by
    refine analyticAt_partialC (analyticAt_Shat hc ha0 ha1 hb0 hb1 hQ0 hQ1)
  have hR : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => Rda H d w.1 w.2.1 w.2.2.1 w.2.2.2) p :=
    analyticAt_Rda H d hc
  simp only [F1]
  exact ((hda.sub hdQ).mul hT).sub (hS.mul hR)

/-- **`F₂` is jointly real-analytic in `(ε,a,b,c)`** under the same hypotheses as
`analyticAt_F1`. -/
theorem analyticAt_F2 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) {p : ℝ × ℝ × ℝ × ℝ} (hc : p.2.2.2 ≠ 1)
    (ha0 : 0 < p.2.1) (ha1 : p.2.1 < 1) (hb0 : 0 < p.2.2.1) (hb1 : p.2.2.1 < 1)
    (hQ0 : 0 < Qmap p.1 p.2.1 p.2.2.1 p.2.2.2) (hQ1 : Qmap p.1 p.2.1 p.2.2.1 p.2.2.2 < 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => F2 H d w.1 w.2.1 w.2.2.1 w.2.2.2) p := by
  have hpb := analyticAt_thd4 p
  have hpc := analyticAt_fth4 p
  have hdb : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => dS0 w.2.2.1) p :=
    AnalyticAt.fun_comp (g := dS0) (f := fun w : ℝ × ℝ × ℝ × ℝ => w.2.2.1)
      (analyticAt_dS0 hb0 hb1) hpb
  have hdQ : AnalyticAt ℝ
      (fun w : ℝ × ℝ × ℝ × ℝ => dS0 (Qmap w.1 w.2.1 w.2.2.1 w.2.2.2)) p :=
    AnalyticAt.fun_comp (g := dS0)
      (f := fun w : ℝ × ℝ × ℝ × ℝ => Qmap w.1 w.2.1 w.2.2.1 w.2.2.2)
      (analyticAt_dS0 hQ0 hQ1) (analyticAt_Qmap hc)
  have hT : AnalyticAt ℝ
      (partialC (fun w : ℝ × ℝ × ℝ × ℝ => That H w.1 w.2.1 w.2.2.1 w.2.2.2)) p :=
    analyticAt_partialC (analyticAt_That H hc)
  have hS : AnalyticAt ℝ
      (partialC (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2)) p :=
    analyticAt_partialC (analyticAt_Shat hc ha0 ha1 hb0 hb1 hQ0 hQ1)
  have hR : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => Rdb H d w.1 w.2.1 w.2.2.1 w.2.2.2) p :=
    analyticAt_Rdb H d hc
  simp only [F2]
  exact (((analyticAt_const.mul (analyticAt_const.sub hpc)).mul (hdb.sub hdQ)).mul hT).sub
    (hS.mul hR)

/-! ### The critical evaluation on the degenerate boundary -/

/-- **The `c = 0` value of the quotient `∂_b𝒯̂/c`**: `Rdb(ε,a,b,0) = n ε^{m-d} 𝒟'_ε(b)`.

At `c = 0` the edge-density solve is `Q = ε` (`Qmap_zero`), so the three summands of `Rdb`
become `-2m ε^{m-1}`, `n d b^{d-1} ε^{m-d}` and `0`, while
`n ε^{m-d}𝒟'_ε(b) = n d b^{d-1}ε^{m-d} - n d ε^{m-1}`.  They agree by the handshake
identity `n d = 2m` (`regular_handshake`) and `ε^{m-d}ε^{d-1} = ε^{m-1}`, which uses
`d ≤ m` (`degree_le_card_edges`). -/
theorem Rdb_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) (ε a b : ℝ) :
    Rdb H d ε a b 0 = (Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * dD d ε b := by
  have hdm : d ≤ H.edgeFinset.card := degree_le_card_edges H hreg (by omega)
  have hnd : (Fintype.card V : ℝ) * (d : ℝ) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast regular_handshake H hreg
  have e2 : ε ^ (H.edgeFinset.card - d) * ε ^ (d - 1) = ε ^ (H.edgeFinset.card - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have key : Rdb H d ε a b 0
      = (H.edgeFinset.card : ℝ) * ε ^ (H.edgeFinset.card - 1) * (-2)
        + (Fintype.card V : ℝ) * ((d : ℝ) * b ^ (d - 1) * ε ^ (H.edgeFinset.card - d)) := by
    simp only [Rdb, Qmap_zero, sub_zero, one_pow, one_mul, mul_one, mul_zero, zero_mul,
      add_zero, div_one]
  rw [key, dD]
  linear_combination ((Fintype.card V : ℝ) * (d : ℝ)) * e2
    + (ε ^ (H.edgeFinset.card - 1)) * hnd

/-- **THE CRITICAL EVALUATION.**  On the degenerate boundary `c = 0`,
`F₂(ε,a,b,0) = n ε^{m-d} Wr_d(ε,b)`, where `Wr` is the numerator of `∂_zψ_d` of
`KRRS/PsiNondeg.lean`.  This is the quotient-free form of the boundary identity
`eq:krrs-quotient-boundary`: the `b`-stationarity of the reduced entropy at `ϑ = 0` is exactly the
scalar KRR–S criticality `∂_zψ_d(ε,b) = 0`.

Note the value does not mention `a` — the first-order entropy gain is independent of `a`. -/
theorem F2_zero_eq {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    F2 H d ε a b 0 = (Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * Wr d ε b := by
  simp only [F2, Qmap_zero, partialC_That_zero H hd hreg hm ε a b,
    partialC_Shat_zero hε0 hε1 ha0 ha1 hb0 hb1, Rdb_zero H hd hreg hm ε a b]
  unfold Afun Wr
  rw [dN_eq_two_mul_dS0]
  ring

/-! ### The three Jacobian entries at `c = 0` -/

/-- **`eq:krrs-jacobian-aa`**: `∂_aF₁|_{c=0} = S₀''(a)·𝒜(ε,b)`.

At `c = 0` the edge-density solve `Q(ε,a,b,0) = ε` does not depend on `a`, so the first
summand of `F₁` is `(S₀'(a) - S₀'(ε))·𝒜(ε,b)`, whose `a`-derivative is `S₀''(a)𝒜(ε,b)`;
and the second summand is `𝒩_ε(b)·Rda(ε,a,b,0)`, which is *constant* in `a` by
`Rda_zero_indep_a`, so contributes nothing. -/
theorem hasDerivAt_F1_a_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    HasDerivAt (fun x => F1 H d ε x b 0)
      ((-1 / (2 * (a * (1 - a)))) * Afun H d ε b) a := by
  have hg : HasDerivAt
      (fun x : ℝ => (dS0 x - dS0 ε) * Afun H d ε b - Nfun ε b * Rda H d ε a b 0)
      ((-1 / (2 * (a * (1 - a)))) * Afun H d ε b) a :=
    (((hasDerivAt_dS0 (ne_of_gt ha0) (ne_of_lt ha1)).sub_const (dS0 ε)).mul_const
      (Afun H d ε b)).sub_const (Nfun ε b * Rda H d ε a b 0)
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ha0 ha1] with x hx
  simp only [F1, Qmap_zero, partialC_That_zero H hd hreg hm ε x b,
    partialC_Shat_zero hε0 hε1 hx.1 hx.2 hb0 hb1, Rda_zero_indep_a H d ε b x a]

/-- **`eq:krrs-jacobian-ba`**: `∂_aF₂|_{c=0} = 0`.  By `F2_zero_eq` the boundary value of `F₂` does
not mention `a` at all, so the function is locally constant in `a`. -/
theorem hasDerivAt_F2_a_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    HasDerivAt (fun x => F2 H d ε x b 0) 0 a := by
  have hg : HasDerivAt
      (fun _ : ℝ => (Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * Wr d ε b) 0 a :=
    hasDerivAt_const a _
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ha0 ha1] with x hx
  exact F2_zero_eq H hd hreg hm hε0 hε1 hx.1 hx.2 hb0 hb1

/-- **`eq:krrs-jacobian-bb`**: `∂_bF₂|_{c=0} = n ε^{m-d} · dWr_d(ε,b)`.

Immediate from `F2_zero_eq` and `hasDerivAt_Wr`; at the KRR–S maximizer the factor
`dWr` is strictly negative by `krrs_scalar_nondegenerate`, which is the paper's
`∂_z²ψ_d(ε_0,z_0)/(n_dε_0^{m-d}) ≠ 0`. -/
theorem hasDerivAt_F2_b_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    HasDerivAt (fun x => F2 H d ε a x 0)
      ((Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * dWr d ε b) b := by
  have hW : HasDerivAt (fun x : ℝ => Wr d ε x) (dWr d ε b) b :=
    hasDerivAt_Wr d ε (ne_of_gt hb0) (ne_of_lt hb1)
  have hg : HasDerivAt
      (fun x : ℝ => (Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * Wr d ε x)
      ((Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * dWr d ε b) b :=
    hW.const_mul _
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hb0 hb1] with x hx
  exact F2_zero_eq H hd hreg hm hε0 hε1 ha0 ha1 hx.1 hx.2

/-! ### The payoff -/

/-- **Paragraph 3's conclusion.**  At the KRR–S base point — `b` an interior maximizer of
`ψ_d(ε,·)` with `b ≠ ε` and `b ≠ r_*` — the desingularized system vanishes in its second
equation and its `(a,b)`-Jacobian at `ϑ = 0` is *triangular with nonzero diagonal*:

* `F₂(ε,a,b,0) = 0` `eq:krrs-boundary-stationarity`;
* `∂_aF₁(ε,a,b,0) = S₀''(a)𝒜(ε,b) ≠ 0` `eq:krrs-jacobian-aa`;
* `∂_aF₂(ε,a,b,0) = 0` `eq:krrs-jacobian-ba`;
* `∂_bF₂(ε,a,b,0) = n ε^{m-d} dWr_d(ε,b) ≠ 0` `eq:krrs-jacobian-bb`.

This is exactly the input the analytic implicit function theorem of `eq:krrs-stationary-densities`
consumes in paragraph 4. -/
theorem F_jacobian_nondegenerate {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hbε : b ≠ ε) (hbstar : b ≠ rStar d)
    (hmax : ∀ w, 0 < w → w < 1 → w ≠ ε → psiD d ε w ≤ psiD d ε b) :
    F2 H d ε a b 0 = 0
      ∧ HasDerivAt (fun x => F1 H d ε x b 0)
          ((-1 / (2 * (a * (1 - a)))) * Afun H d ε b) a
      ∧ (-1 / (2 * (a * (1 - a)))) * Afun H d ε b ≠ 0
      ∧ HasDerivAt (fun x => F2 H d ε x b 0) 0 a
      ∧ HasDerivAt (fun x => F2 H d ε a x 0)
          ((Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * dWr d ε b) b
      ∧ (Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * dWr d ε b ≠ 0 := by
  obtain ⟨hWr, hdWr⟩ :=
    krrs_scalar_nondegenerate hd hε0 hb.1 hb.2 hbε hbstar hmax
  have : Nonempty V := nonempty_of_edge H (by omega)
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < ε ^ (H.edgeFinset.card - d) := pow_pos hε0 _
  refine ⟨?_, hasDerivAt_F1_a_zero H hd hreg hm hε0 hε1 ha.1 ha.2 hb.1 hb.2, ?_,
    hasDerivAt_F2_a_zero H hd hreg hm hε0 hε1 ha.1 ha.2 hb.1 hb.2,
    hasDerivAt_F2_b_zero H hd hreg hm hε0 hε1 ha.1 ha.2 hb.1 hb.2, ?_⟩
  · rw [F2_zero_eq H hd hreg hm hε0 hε1 ha.1 ha.2 hb.1 hb.2, hWr, mul_zero]
  · -- `S₀''(a) < 0` and `𝒜(ε,b) > 0`, so the product is strictly negative
    have hA : 0 < Afun H d ε b := Afun_pos H hd (by omega) hε0 hb.1.le hbε
    have hden : (0 : ℝ) < 2 * (a * (1 - a)) := by
      have : (0 : ℝ) < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
      linarith
    have hS : (-1 : ℝ) / (2 * (a * (1 - a))) < 0 := div_neg_of_neg_of_pos (by norm_num) hden
    exact ne_of_lt (mul_neg_of_neg_of_pos hS hA)
  · exact ne_of_lt (mul_neg_of_pos_of_neg (mul_pos hn hpow) hdWr)

end UpperTailOptimizers
