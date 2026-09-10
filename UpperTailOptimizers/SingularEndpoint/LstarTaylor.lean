import UpperTailOptimizers.SingularEndpoint.Fkkt4

/-!
# Analyticity and the singular endpoint Taylor data of `𝓛_*` and `Γ_d` (Section 7, `paper/singular_endpoint.tex`)

`SingularEndpoint/Contact.lean` and `SingularEndpoint/Fkkt4.lean` differentiate the KKT
function `𝓛_*(z) = J_{p_*}'(z) - γ_* z^{d-1}` of `eq:kkt-quartic-expansion` four times and
evaluate the results at the exceptional density `r_*`: that is the content of the triple
contact `eq:endpoint-entropy-derivatives`, of `𝓛_*'''(r_*) = d⁵/(d-1)²`, and of
`𝓛_*^{(4)}(r_*) = 5d⁶(d-2)/(d-1)³`.  Those statements are `HasDerivAt` facts relating the
*separately defined* functions `Lstar`, `Lstar1`, …, `Lstar4`.

What the `h⁵` bookkeeping of `sec:singular-endpoint` consumes is the same data in
*Taylor* form: a power-series remainder is stated in terms of `iteratedDeriv k f a`, not in
terms of a hand-written chain of auxiliary functions.  This file supplies the bridge, and
the analyticity that makes a Taylor expansion available at all:

```
Γ_d^{(j)}(r_*) = 0  (0 ≤ j ≤ 3),   Γ_d^{(4)}(r_*) = d⁵/(d-1)²,
Γ_d^{(5)}(r_*) = 5d⁶(d-2)/(d-1)³,
```

which are `eq:endpoint-gap-expansion` and — for the quintic value —
`eq:kkt-quartic-expansion` in the appendix's "Proof of the parameter expansions"
(`app:rank-one-parameter-expansions`; the `𝓛₀` there is `𝓛_*`), and
their one-order-lower counterparts for `𝓛_* = Γ_d'`.

**How the identification is made.**  `iteratedDeriv (k+1) f = deriv (iteratedDeriv k f)`
only ever reads `iteratedDeriv k f` near the evaluation point, so it is enough to know each
`iteratedDeriv k (Lstar d)` *on a neighbourhood* of `r_*`.  Since `Set.Ioo 0 1` is such a
neighbourhood (`rStar_pos`, `rStar_lt_one`) and every link of the `HasDerivAt` chain holds
throughout `Set.Ioo 0 1`, the private lemmas below propagate the eventual equalities
`iteratedDeriv k (Lstar d) =ᶠ[𝓝 r_*] Lstar_k d` upwards one order at a time, using
`Filter.EventuallyEq.deriv`.  Evaluating at `r_*` then just quotes `Contact.lean` and
`Fkkt4.lean`.  Nothing here needs the derivative values off `Set.Ioo 0 1`, where `deriv`
returns junk.

## Contents

* `analyticAt_Lstar`, `analyticOnNhd_Lstar`, `analyticAt_Gam`, `analyticOnNhd_Gam` — both
  functions are real-analytic on `(0,1)`;
* `iteratedDeriv_one_Lstar`, `iteratedDeriv_two_Lstar`, `iteratedDeriv_three_Lstar`,
  `iteratedDeriv_four_Lstar` — the Taylor data of `𝓛_*` at `r_*`;
* `iteratedDeriv_one_Gam`, …, `iteratedDeriv_five_Gam` — the Taylor data of `Γ_d` at `r_*`,
  the same list shifted by one because `Γ_d' = 𝓛_*`.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open Real Filter Topology

variable {d : ℕ}

/-! ## Analyticity of the scalar ingredients

`J_p'` and `J_p` are compositions of `Real.log` with rational functions whose arguments are
positive on `(0,1)`, so `AnalyticAt.log` applies directly.  These are stated for a general
`p ∈ (0,1)` and instantiated at `p_*` below. -/

/-- `J_p'(z) = log(z(1-p)/((1-z)p))` is analytic at every `z ∈ (0,1)`: the argument of the
logarithm is a quotient of affine functions with non-vanishing denominator, and it is
positive at `z`. -/
private theorem analyticAt_Jp' {p z : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hz0 : 0 < z)
    (hz1 : z < 1) : AnalyticAt ℝ (Jp' p) z := by
  have h1z : (0 : ℝ) < 1 - z := by linarith
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hinner : AnalyticAt ℝ (fun y : ℝ => y * (1 - p) / ((1 - y) * p)) z :=
    (analyticAt_id.mul analyticAt_const).div
      ((analyticAt_const.sub analyticAt_id).mul analyticAt_const) (ne_of_gt (mul_pos h1z hp0))
  show AnalyticAt ℝ (fun y : ℝ => Real.log (y * (1 - p) / ((1 - y) * p))) z
  exact hinner.log (div_pos (mul_pos hz0 h1p) (mul_pos h1z hp0))

/-- `J_p(z) = z log(z/p) + (1-z) log((1-z)/(1-p))` is analytic at every `z ∈ (0,1)`: both
logarithms have positive analytic arguments there, and the prefactors are affine. -/
private theorem analyticAt_Jp {p z : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hz0 : 0 < z)
    (hz1 : z < 1) : AnalyticAt ℝ (Jp p) z := by
  have h1z : (0 : ℝ) < 1 - z := by linarith
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hA : AnalyticAt ℝ (fun y : ℝ => Real.log (y / p)) z :=
    (analyticAt_id.div analyticAt_const (ne_of_gt hp0)).log (div_pos hz0 hp0)
  have hB : AnalyticAt ℝ (fun y : ℝ => Real.log ((1 - y) / (1 - p))) z :=
    ((analyticAt_const.sub analyticAt_id).div analyticAt_const (ne_of_gt h1p)).log
      (div_pos h1z h1p)
  show AnalyticAt ℝ
    (fun y : ℝ => y * Real.log (y / p) + (1 - y) * Real.log ((1 - y) / (1 - p))) z
  exact (analyticAt_id.mul hA).add ((analyticAt_const.sub analyticAt_id).mul hB)

/-! ## Analyticity of `𝓛_*` and `Γ_d` -/

/-- **`𝓛_*` is real-analytic on `(0,1)`.**  Adding the monomial `γ_* z^{d-1}` to the
analytic `J_{p_*}'` cannot destroy analyticity, and `p_* ∈ (0,1)`. -/
theorem analyticAt_Lstar (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    AnalyticAt ℝ (Lstar d) z := by
  have hpow : AnalyticAt ℝ (fun y : ℝ => gammaStar d * y ^ (d - 1)) z :=
    analyticAt_const.mul (analyticAt_id.pow (d - 1))
  show AnalyticAt ℝ (fun y : ℝ => Jp' (pStar d) y - gammaStar d * y ^ (d - 1)) z
  exact (analyticAt_Jp' (pStar_pos hd) (pStar_lt_one hd) hz0 hz1).sub hpow

/-- The set form of `analyticAt_Lstar`, which is what the Taylor-series machinery of
`SingularEndpoint/Quotient.lean` and its consumers take as input. -/
theorem analyticOnNhd_Lstar (hd : 2 ≤ d) : AnalyticOnNhd ℝ (Lstar d) (Set.Ioo (0 : ℝ) 1) :=
  fun _ hz => analyticAt_Lstar hd hz.1 hz.2

/-- **`Γ_d` is real-analytic on `(0,1)`.**  The singular endpoint supporting gap
`Γ_d(z) = J_{p_*}(z) - J_{p_*}(r_*) - β_d(z^d - r_*^d)` of `eq:endpoint-supporting-gap`
differs from `J_{p_*}` by a polynomial. -/
theorem analyticAt_Gam (hd : 2 ≤ d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    AnalyticAt ℝ (Gam d) z := by
  have hpoly : AnalyticAt ℝ (fun y : ℝ => betaD d * (y ^ d - rStar d ^ d)) z :=
    analyticAt_const.mul ((analyticAt_id.pow d).sub analyticAt_const)
  show AnalyticAt ℝ
    (fun y : ℝ => Jp (pStar d) y - Jp (pStar d) (rStar d) - betaD d * (y ^ d - rStar d ^ d)) z
  exact ((analyticAt_Jp (pStar_pos hd) (pStar_lt_one hd) hz0 hz1).sub analyticAt_const).sub hpoly

/-- The set form of `analyticAt_Gam`. -/
theorem analyticOnNhd_Gam (hd : 2 ≤ d) : AnalyticOnNhd ℝ (Gam d) (Set.Ioo (0 : ℝ) 1) :=
  fun _ hz => analyticAt_Gam hd hz.1 hz.2

/-! ## Propagating the derivative chain to `iteratedDeriv`

Two small devices do all the work.  `deriv_eventuallyEq_of_hasDerivAt` turns a `HasDerivAt`
statement valid throughout `(0,1)` into an identification of `deriv` on a neighbourhood of
`r_*`; `deriv_eventuallyEq_step` composes that with `Filter.EventuallyEq.deriv` so that an
identification already obtained at order `k` can be differentiated to give order `k+1`. -/

/-- `(0,1)` is a neighbourhood of the exceptional density. -/
private theorem Ioo_mem_nhds_rStar (hd : 2 ≤ d) : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 (rStar d) :=
  Ioo_mem_nhds (rStar_pos hd) (rStar_lt_one hd)

/-- If `g' = h` in the `HasDerivAt` sense throughout `(0,1)`, then `deriv g` agrees with `h`
near `r_*`.  Only the neighbourhood statement is available: off `(0,1)` the function `deriv g`
is Lean's junk value. -/
private theorem deriv_eventuallyEq_of_hasDerivAt (hd : 2 ≤ d) {g h : ℝ → ℝ}
    (hgh : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (h z) z) :
    deriv g =ᶠ[𝓝 (rStar d)] h :=
  Filter.eventuallyEq_of_mem (Ioo_mem_nhds_rStar hd) fun z hz => (hgh z hz).deriv

/-- One rung of the ladder: if `F` agrees with `G` near `r_*` and `G' = H` on `(0,1)`, then
`deriv F` agrees with `H` near `r_*`. -/
private theorem deriv_eventuallyEq_step (hd : 2 ≤ d) {F G H : ℝ → ℝ}
    (hFG : F =ᶠ[𝓝 (rStar d)] G) (hGH : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt G (H z) z) :
    deriv F =ᶠ[𝓝 (rStar d)] H :=
  hFG.deriv.trans (deriv_eventuallyEq_of_hasDerivAt hd hGH)

/-! ### The `𝓛_*` ladder -/

/-- `𝓛_*^{(1)} = 𝓛_*'` near `r_*`. -/
private theorem iteratedDeriv_one_Lstar_eventuallyEq (hd : 2 ≤ d) :
    iteratedDeriv 1 (Lstar d) =ᶠ[𝓝 (rStar d)] Lstar1 d := by
  rw [iteratedDeriv_one]
  exact deriv_eventuallyEq_of_hasDerivAt hd fun _ hz => hasDerivAt_Lstar hd hz.1 hz.2

/-- `𝓛_*^{(2)} = 𝓛_*''` near `r_*`. -/
private theorem iteratedDeriv_two_Lstar_eventuallyEq (hd : 2 ≤ d) :
    iteratedDeriv 2 (Lstar d) =ᶠ[𝓝 (rStar d)] Lstar2 d := by
  rw [iteratedDeriv_succ]
  exact deriv_eventuallyEq_step hd (iteratedDeriv_one_Lstar_eventuallyEq hd)
    fun _ hz => hasDerivAt_Lstar1 hd hz.1 hz.2

/-- `𝓛_*^{(3)} = 𝓛_*'''` near `r_*`. -/
private theorem iteratedDeriv_three_Lstar_eventuallyEq (hd : 2 ≤ d) :
    iteratedDeriv 3 (Lstar d) =ᶠ[𝓝 (rStar d)] Lstar3 d := by
  rw [iteratedDeriv_succ]
  exact deriv_eventuallyEq_step hd (iteratedDeriv_two_Lstar_eventuallyEq hd)
    fun _ hz => hasDerivAt_Lstar2 hd hz.1 hz.2

/-- `𝓛_*^{(4)}` near `r_*`, the top of the chain supplied by `SingularEndpoint/Fkkt4.lean`. -/
private theorem iteratedDeriv_four_Lstar_eventuallyEq (hd : 2 ≤ d) :
    iteratedDeriv 4 (Lstar d) =ᶠ[𝓝 (rStar d)] Lstar4 d := by
  rw [iteratedDeriv_succ]
  exact deriv_eventuallyEq_step hd (iteratedDeriv_three_Lstar_eventuallyEq hd)
    fun _ hz => hasDerivAt_Lstar3 hd hz.1 hz.2

/-! ### The `Γ_d` ladder

`Γ_d' = 𝓛_*` on `(0,1)` (`hasDerivAt_Gam`), so the `Γ_d` ladder is the `𝓛_*` ladder started
one rung lower; it is rebuilt here rather than transported, which costs one line per order
and avoids an induction over `iteratedDeriv` of eventually-equal functions. -/

/-- `Γ_d^{(1)} = 𝓛_*` near `r_*`. -/
private theorem iteratedDeriv_one_Gam_eventuallyEq (hd : 2 ≤ d) :
    iteratedDeriv 1 (Gam d) =ᶠ[𝓝 (rStar d)] Lstar d := by
  rw [iteratedDeriv_one]
  exact deriv_eventuallyEq_of_hasDerivAt hd fun _ hz => hasDerivAt_Gam hd hz.1 hz.2

/-- `Γ_d^{(2)} = 𝓛_*'` near `r_*`. -/
private theorem iteratedDeriv_two_Gam_eventuallyEq (hd : 2 ≤ d) :
    iteratedDeriv 2 (Gam d) =ᶠ[𝓝 (rStar d)] Lstar1 d := by
  rw [iteratedDeriv_succ]
  exact deriv_eventuallyEq_step hd (iteratedDeriv_one_Gam_eventuallyEq hd)
    fun _ hz => hasDerivAt_Lstar hd hz.1 hz.2

/-- `Γ_d^{(3)} = 𝓛_*''` near `r_*`. -/
private theorem iteratedDeriv_three_Gam_eventuallyEq (hd : 2 ≤ d) :
    iteratedDeriv 3 (Gam d) =ᶠ[𝓝 (rStar d)] Lstar2 d := by
  rw [iteratedDeriv_succ]
  exact deriv_eventuallyEq_step hd (iteratedDeriv_two_Gam_eventuallyEq hd)
    fun _ hz => hasDerivAt_Lstar1 hd hz.1 hz.2

/-- `Γ_d^{(4)} = 𝓛_*'''` near `r_*`. -/
private theorem iteratedDeriv_four_Gam_eventuallyEq (hd : 2 ≤ d) :
    iteratedDeriv 4 (Gam d) =ᶠ[𝓝 (rStar d)] Lstar3 d := by
  rw [iteratedDeriv_succ]
  exact deriv_eventuallyEq_step hd (iteratedDeriv_three_Gam_eventuallyEq hd)
    fun _ hz => hasDerivAt_Lstar2 hd hz.1 hz.2

/-- `Γ_d^{(5)} = 𝓛_*^{(4)}` near `r_*`. -/
private theorem iteratedDeriv_five_Gam_eventuallyEq (hd : 2 ≤ d) :
    iteratedDeriv 5 (Gam d) =ᶠ[𝓝 (rStar d)] Lstar4 d := by
  rw [iteratedDeriv_succ]
  exact deriv_eventuallyEq_step hd (iteratedDeriv_four_Gam_eventuallyEq hd)
    fun _ hz => hasDerivAt_Lstar3 hd hz.1 hz.2

/-! ## The Taylor data at `r_*`

The `𝓛_*` list is the triple contact `eq:endpoint-entropy-derivatives` read as "`𝓛_*`
vanishes to order exactly three at `r_*`", plus the fourth coefficient of
`SingularEndpoint/Fkkt4.lean`. -/

/-- `𝓛_*'(r_*) = 0`: the second of the triple-contact identities. -/
theorem iteratedDeriv_one_Lstar (hd : 2 ≤ d) : iteratedDeriv 1 (Lstar d) (rStar d) = 0 := by
  rw [(iteratedDeriv_one_Lstar_eventuallyEq hd).eq_of_nhds]
  exact Lstar1_rStar hd

/-- `𝓛_*''(r_*) = 0`: the third of the triple-contact identities. -/
theorem iteratedDeriv_two_Lstar (hd : 2 ≤ d) : iteratedDeriv 2 (Lstar d) (rStar d) = 0 := by
  rw [(iteratedDeriv_two_Lstar_eventuallyEq hd).eq_of_nhds]
  exact Lstar2_rStar hd

/-- `𝓛_*'''(r_*) = d⁵/(d-1)²`: the non-degeneracy constant of
`eq:endpoint-gap-expansion`. -/
theorem iteratedDeriv_three_Lstar (hd : 2 ≤ d) :
    iteratedDeriv 3 (Lstar d) (rStar d) = (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 := by
  rw [(iteratedDeriv_three_Lstar_eventuallyEq hd).eq_of_nhds]
  exact Lstar3_rStar hd

/-- `𝓛_*^{(4)}(r_*) = 5d⁶(d-2)/(d-1)³`, the coefficient behind `eq:kkt-quartic-expansion`
(`app:rank-one-parameter-expansions`; the appendix writes `𝓛₀` for `𝓛_*`). -/
theorem iteratedDeriv_four_Lstar (hd : 2 ≤ d) :
    iteratedDeriv 4 (Lstar d) (rStar d) = 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 := by
  rw [(iteratedDeriv_four_Lstar_eventuallyEq hd).eq_of_nhds]
  exact Lstar4_rStar hd

/-- `Γ_d'(r_*) = 0`: the supporting line of `eq:endpoint-supporting-gap` is tangent at
`r_*`. -/
theorem iteratedDeriv_one_Gam (hd : 2 ≤ d) : iteratedDeriv 1 (Gam d) (rStar d) = 0 := by
  rw [(iteratedDeriv_one_Gam_eventuallyEq hd).eq_of_nhds]
  exact Lstar_rStar hd

/-- `Γ_d''(r_*) = 0`. -/
theorem iteratedDeriv_two_Gam (hd : 2 ≤ d) : iteratedDeriv 2 (Gam d) (rStar d) = 0 := by
  rw [(iteratedDeriv_two_Gam_eventuallyEq hd).eq_of_nhds]
  exact Lstar1_rStar hd

/-- `Γ_d'''(r_*) = 0`.  Together with `Gam_rStar`, `iteratedDeriv_one_Gam` and
`iteratedDeriv_two_Gam` this is the vanishing `Γ_d^{(j)}(r_*) = 0` for `0 ≤ j ≤ 3` quoted
before `eq:endpoint-gap-expansion`. -/
theorem iteratedDeriv_three_Gam (hd : 2 ≤ d) : iteratedDeriv 3 (Gam d) (rStar d) = 0 := by
  rw [(iteratedDeriv_three_Gam_eventuallyEq hd).eq_of_nhds]
  exact Lstar2_rStar hd

/-- **`Γ_d^{(4)}(r_*) = d⁵/(d-1)²`**, the leading Taylor coefficient of
`eq:endpoint-gap-expansion`: `Γ_d(r_* + z) = d⁵z⁴/(24(d-1)²) + O(z⁵)`. -/
theorem iteratedDeriv_four_Gam (hd : 2 ≤ d) :
    iteratedDeriv 4 (Gam d) (rStar d) = (d : ℝ) ^ 5 / ((d : ℝ) - 1) ^ 2 := by
  rw [(iteratedDeriv_four_Gam_eventuallyEq hd).eq_of_nhds]
  exact Lstar3_rStar hd

/-- **`Γ_d^{(5)}(r_*) = 5d⁶(d-2)/(d-1)³`**, which is the quartic coefficient of
`eq:kkt-quartic-expansion` read through `𝓛₀ = Γ_d'` (Appendix E.2); it is
the `z⁵` coefficient `d⁶(d-2)/(24(d-1)³)` of the expansion of `Γ_d(r_* + z)`. -/
theorem iteratedDeriv_five_Gam (hd : 2 ≤ d) :
    iteratedDeriv 5 (Gam d) (rStar d) = 5 * (d : ℝ) ^ 6 * ((d : ℝ) - 2) / ((d : ℝ) - 1) ^ 3 := by
  rw [(iteratedDeriv_five_Gam_eventuallyEq hd).eq_of_nhds]
  exact Lstar4_rStar hd

end SingularEndpoint

end UpperTailOptimizers
