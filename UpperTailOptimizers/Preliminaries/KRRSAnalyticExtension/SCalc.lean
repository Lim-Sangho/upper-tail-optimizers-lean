import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.Reduced

/-!
# The entropy derivatives of Appendix B

This file carries out the entropy computations for Appendix B of `paper/paper.tex`: the
boundary derivative `eq:krrs-entropy-derivative` of paragraph 2, and the *exact* `a`- and
`b`-derivatives used by this formalisation's stationarity system, all for the edge-constrained
entropy

`Ŝ(ε,a,b,c) = c²S₀(a) + 2c(1-c)S₀(b) + (1-c)²S₀(Q(ε,a,b,c))`,

where `Q` is the edge-density solve `eq:krrs-edge-constraint` of `Preliminaries/KRRSAnalyticExtension/Reduced.lean`.

## Contents

* `hasDerivAt_Qmap_a`, `hasDerivAt_Qmap_b` — the two partial derivatives of `Q` that the
  entropy (and later the `H`-density) computation needs:
  `∂_aQ = -c²/(1-c)²` and `∂_bQ = -2c/(1-c)`.
* `hasDerivAt_Shat_a`, `hasDerivAt_Shat_b` — the exact formulas
  `∂_aŜ = c²[S₀'(a) - S₀'(Q)]` and `∂_bŜ = 2c(1-c)[S₀'(b) - S₀'(Q)]`.  They are exact,
  not merely asymptotic: the prefactor `(1-c)²` of `S₀(Q)` cancels the denominator of
  `∂_aQ`, resp. `∂_bQ`.  The visible factor `c²` in the `a`-derivative is what
  desingularises the `c`-normalised stationarity equation of `Preliminaries/KRRSAnalyticExtension/Stationarity.lean` (the
  paper desingularises in the excess `ϑ` instead, through `eq:krrs-entropy-quotient`).
* `hasDerivAt_Shat_c_zero` — `∂_cŜ|_{c=0} = 𝒩_ε(b)` `eq:krrs-entropy-derivative`, the
  first-order entropy gain of tilting mass into the first pode.
* `analyticAt_Shat` — joint real-analyticity of `Ŝ` in `(ε,a,b,c)`, the analyticity input for
  the reduced entropy `Σ` and the stationarity functions of `Preliminaries/KRRSAnalyticExtension/Stationarity.lean`.
-/

namespace UpperTailOptimizers

open Real Filter Topology

/-! ### The partial derivatives of `Q` -/

/-- `∂_aQ = -c²/(1-c)²`.  Only the numerator of `Q` depends on `a`, and it does so
affinely, so no hypothesis on `c` is needed. -/
theorem hasDerivAt_Qmap_a (ε b c a : ℝ) :
    HasDerivAt (fun x => Qmap ε x b c) (-c ^ 2 / (1 - c) ^ 2) a := by
  have hnum : HasDerivAt (fun x : ℝ => ε - c ^ 2 * x - 2 * c * (1 - c) * b) (-c ^ 2) a := by
    have h : HasDerivAt (fun x : ℝ => c ^ 2 * x) (c ^ 2) a := by
      simpa using (hasDerivAt_id a).const_mul (c ^ 2)
    simpa using ((hasDerivAt_const a ε).sub h).sub_const (2 * c * (1 - c) * b)
  have h := hnum.div_const ((1 - c) ^ 2)
  have hQ : (fun x => Qmap ε x b c)
      = fun x : ℝ => (ε - c ^ 2 * x - 2 * c * (1 - c) * b) / (1 - c) ^ 2 := rfl
  rw [hQ]
  exact h

/-- `∂_bQ = -2c/(1-c)`: one factor `(1-c)` of the numerator cancels against the
denominator `(1-c)²`. -/
theorem hasDerivAt_Qmap_b {c : ℝ} (hc : c ≠ 1) (ε a b : ℝ) :
    HasDerivAt (fun x => Qmap ε a x c) (-2 * c / (1 - c)) b := by
  have hc' : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hnum : HasDerivAt (fun x : ℝ => ε - c ^ 2 * a - 2 * c * (1 - c) * x)
      (-(2 * c * (1 - c))) b := by
    have h : HasDerivAt (fun x : ℝ => 2 * c * (1 - c) * x) (2 * c * (1 - c)) b := by
      simpa using (hasDerivAt_id b).const_mul (2 * c * (1 - c))
    simpa using ((hasDerivAt_const b ε).sub_const (c ^ 2 * a)).fun_sub h
  have h := hnum.div_const ((1 - c) ^ 2)
  have hQ : (fun x => Qmap ε a x c)
      = fun x : ℝ => (ε - c ^ 2 * a - 2 * c * (1 - c) * x) / (1 - c) ^ 2 := rfl
  rw [hQ]
  convert h using 1
  all_goals try rfl
  field_simp

/-! ### The exact `a`- and `b`-derivatives of `Ŝ` -/

/-- `∂_a Ŝ = c²[S₀'(a) - S₀'(Q)]`: the `a`-dependence of the entropy is exactly of
order `c²`, which is what desingularises the `c`-normalised stationarity equation `F1` of
`Preliminaries/KRRSAnalyticExtension/Stationarity.lean`. -/
theorem hasDerivAt_Shat_a {ε a b c : ℝ} (hc : c ≠ 1)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hQ0 : Qmap ε a b c ≠ 0) (hQ1 : Qmap ε a b c ≠ 1) :
    HasDerivAt (fun x => Shat ε x b c) (c ^ 2 * (dS0 a - dS0 (Qmap ε a b c))) a := by
  have hc' : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have h1 : HasDerivAt (fun x : ℝ => c ^ 2 * S0 x) (c ^ 2 * dS0 a) a :=
    (hasDerivAt_S0 ha0 ha1).const_mul (c ^ 2)
  have h2 : HasDerivAt (fun _ : ℝ => 2 * c * (1 - c) * S0 b) 0 a :=
    hasDerivAt_const a (2 * c * (1 - c) * S0 b)
  have hQa : HasDerivAt (fun x => Qmap ε x b c) (-c ^ 2 / (1 - c) ^ 2) a :=
    hasDerivAt_Qmap_a ε b c a
  have h3 : HasDerivAt (fun x : ℝ => (1 - c) ^ 2 * S0 (Qmap ε x b c))
      ((1 - c) ^ 2 * (dS0 (Qmap ε a b c) * (-c ^ 2 / (1 - c) ^ 2))) a :=
    (((hasDerivAt_S0 hQ0 hQ1).comp a hQa)).const_mul ((1 - c) ^ 2)
  have h := (h1.add h2).add h3
  have hS : (fun x => Shat ε x b c)
      = fun x : ℝ => c ^ 2 * S0 x + 2 * c * (1 - c) * S0 b
          + (1 - c) ^ 2 * S0 (Qmap ε x b c) := rfl
  rw [hS]
  convert h using 1
  all_goals try rfl
  field_simp
  ring

/-- `∂_b Ŝ = 2c(1-c)[S₀'(b) - S₀'(Q)]`. -/
theorem hasDerivAt_Shat_b {ε a b c : ℝ} (hc : c ≠ 1)
    (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hQ0 : Qmap ε a b c ≠ 0) (hQ1 : Qmap ε a b c ≠ 1) :
    HasDerivAt (fun x => Shat ε a x c) (2 * c * (1 - c) * (dS0 b - dS0 (Qmap ε a b c))) b := by
  have hc' : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have h1 : HasDerivAt (fun _ : ℝ => c ^ 2 * S0 a) 0 b := hasDerivAt_const b (c ^ 2 * S0 a)
  have h2 : HasDerivAt (fun x : ℝ => 2 * c * (1 - c) * S0 x) (2 * c * (1 - c) * dS0 b) b :=
    (hasDerivAt_S0 hb0 hb1).const_mul (2 * c * (1 - c))
  have hQb : HasDerivAt (fun x => Qmap ε a x c) (-2 * c / (1 - c)) b :=
    hasDerivAt_Qmap_b hc ε a b
  have h3 : HasDerivAt (fun x : ℝ => (1 - c) ^ 2 * S0 (Qmap ε a x c))
      ((1 - c) ^ 2 * (dS0 (Qmap ε a b c) * (-2 * c / (1 - c)))) b :=
    (((hasDerivAt_S0 hQ0 hQ1).comp b hQb)).const_mul ((1 - c) ^ 2)
  have h := (h1.add h2).add h3
  have hS : (fun x => Shat ε a x c)
      = fun x : ℝ => c ^ 2 * S0 a + 2 * c * (1 - c) * S0 x
          + (1 - c) ^ 2 * S0 (Qmap ε a x c) := rfl
  rw [hS]
  convert h using 1
  all_goals try rfl
  field_simp
  ring

/-! ### The `c`-derivative at the singular endpoint -/

/-- `∂_c Ŝ|_{c=0} = 𝒩_ε(b)` `eq:krrs-entropy-derivative`.  The three summands of `Ŝ`
contribute `0`, `2S₀(b)` and `-2S₀(ε) + 2S₀'(ε)(ε-b)` respectively, and the sum is exactly
`𝒩_ε(b) = 2[S₀(b) - S₀(ε) - S₀'(ε)(b-ε)]`. -/
theorem hasDerivAt_Shat_c_zero {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (a b : ℝ) :
    HasDerivAt (fun c => Shat ε a b c) (Nfun ε b) 0 := by
  have h1 : HasDerivAt (fun c : ℝ => c ^ 2 * S0 a) 0 (0 : ℝ) := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const (S0 a)
  have h2 : HasDerivAt (fun c : ℝ => 2 * c * (1 - c) * S0 b) (2 * S0 b) (0 : ℝ) := by
    simpa using (hasDerivAt_two_mul_one_sub (0 : ℝ)).mul_const (S0 b)
  have hsq : HasDerivAt (fun c : ℝ => (1 - c) ^ 2) (-2) (0 : ℝ) := by
    simpa using hasDerivAt_one_sub_sq (0 : ℝ)
  have hS0Q : HasDerivAt S0 (dS0 (Qmap ε a b 0)) (Qmap ε a b 0) := by
    rw [Qmap_zero]
    exact hasDerivAt_S0 (ne_of_gt hε0) (ne_of_lt hε1)
  have hcomp : HasDerivAt (fun c : ℝ => S0 (Qmap ε a b c))
      (dS0 (Qmap ε a b 0) * (2 * (ε - b))) (0 : ℝ) :=
    hS0Q.comp 0 (hasDerivAt_Qmap_c ε a b)
  have h3 : HasDerivAt (fun c : ℝ => (1 - c) ^ 2 * S0 (Qmap ε a b c))
      (-2 * S0 (Qmap ε a b 0)
        + (1 - (0 : ℝ)) ^ 2 * (dS0 (Qmap ε a b 0) * (2 * (ε - b)))) (0 : ℝ) :=
    hsq.mul hcomp
  have h := (h1.add h2).add h3
  have hS : (fun c => Shat ε a b c)
      = fun c : ℝ => c ^ 2 * S0 a + 2 * c * (1 - c) * S0 b
          + (1 - c) ^ 2 * S0 (Qmap ε a b c) := rfl
  rw [hS]
  convert h using 1
  all_goals try rfl
  simp only [Qmap_zero, Nfun]
  ring

/-! ### Joint analyticity -/

/-- `Ŝ` is jointly real-analytic in `(ε,a,b,c)` wherever `c ≠ 1` and the three block
densities `a`, `b`, `Q(ε,a,b,c)` lie in `(0,1)`.  This is the regularity input for the
analytic implicit function theorem that produces `C` of `eq:krrs-density-constraint`. -/
theorem analyticAt_Shat {p : ℝ × ℝ × ℝ × ℝ}
    (hc : p.2.2.2 ≠ 1) (ha : 0 < p.2.1) (ha1 : p.2.1 < 1)
    (hb : 0 < p.2.2.1) (hb1 : p.2.2.1 < 1)
    (hQ : 0 < Qmap p.1 p.2.1 p.2.2.1 p.2.2.2) (hQ1 : Qmap p.1 p.2.1 p.2.2.1 p.2.2.2 < 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2) p := by
  have hpa := analyticAt_snd4 p
  have hpb := analyticAt_thd4 p
  have hpc := analyticAt_fth4 p
  have hSa : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => S0 w.2.1) p :=
    AnalyticAt.fun_comp (g := S0) (f := fun w : ℝ × ℝ × ℝ × ℝ => w.2.1)
      (analyticAt_S0 ha ha1) hpa
  have hSb : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => S0 w.2.2.1) p :=
    AnalyticAt.fun_comp (g := S0) (f := fun w : ℝ × ℝ × ℝ × ℝ => w.2.2.1)
      (analyticAt_S0 hb hb1) hpb
  have hSQ : AnalyticAt ℝ
      (fun w : ℝ × ℝ × ℝ × ℝ => S0 (Qmap w.1 w.2.1 w.2.2.1 w.2.2.2)) p :=
    AnalyticAt.fun_comp (g := S0)
      (f := fun w : ℝ × ℝ × ℝ × ℝ => Qmap w.1 w.2.1 w.2.2.1 w.2.2.2)
      (analyticAt_S0 hQ hQ1) (analyticAt_Qmap hc)
  have hfun : (fun w : ℝ × ℝ × ℝ × ℝ => Shat w.1 w.2.1 w.2.2.1 w.2.2.2)
      = fun w : ℝ × ℝ × ℝ × ℝ => w.2.2.2 ^ 2 * S0 w.2.1
          + 2 * w.2.2.2 * (1 - w.2.2.2) * S0 w.2.2.1
          + (1 - w.2.2.2) ^ 2 * S0 (Qmap w.1 w.2.1 w.2.2.1 w.2.2.2) := rfl
  rw [hfun]
  exact (((hpc.pow 2).mul hSa).add
    (((analyticAt_const.mul hpc).mul (analyticAt_const.sub hpc)).mul hSb)).add
    (((analyticAt_const.sub hpc).pow 2).mul hSQ)

end UpperTailOptimizers
