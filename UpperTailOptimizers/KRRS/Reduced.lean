import UpperTailOptimizers.KRRS.Chart
import UpperTailOptimizers.LZBoundary.AnalyticEntropy
import UpperTailOptimizers.Graphon.ScalarEntropy

/-!
# The scalar objects of Appendix A

Appendix A of `paper/bipodal_optimizer.tex` (Appendix A) runs a finite-dimensional
calculation in the four bipodal parameters.  This file sets up the scalar functions it
uses — everything that appears in its paragraphs 1 and 2 as a *definition* — together
with their derivatives and analyticity.  Nothing here is assumed; the two KRR–S inputs
live in `KRRS/Inputs.lean`.

## Contents

* `S0`, `dS0` — the paper's `S₀(u) = -½[u log u + (1-u) log(1-u)]` and its derivative.
  `S0 = shannonH / 2`, so the project's block-entropy formula `bipEnt` is exactly the
  paper's `Ŝ`; `dN_eq_two_mul_dS0` records the resulting factor `2` between `𝒩'` and `S₀'`.
* `hasDerivAt_two_mul_one_sub`, `hasDerivAt_one_sub_sq` — the derivatives of the two block
  weights `2c(1-c)` and `(1-c)²`, shared by the `c`-derivative computations.
* `Nfun`, `Dfun`, `psiD` — the paper's `𝒩_ε(z)`, `𝒟_ε(z)` and
  `ψ_d(ε,z) = 𝒩_ε(z)/𝒟_ε(z)` (`eq:krrs-entropy-remainder`, `eq:krrs-moment-remainder`), with their first three
  `z`-derivatives.
* `Qmap` — the paper's `Q(ε,a,b,c)` of `eq:krrs-edge-constraint`, the unique `q₂₂` giving
  edge density `ε`, with `bipEdge_Qmap` and the expansion value `∂_cQ|_{c=0} = 2(ε-b)`.
* `That`, `Shat` — the edge-constrained `H`-density and entropy `𝒯̂`, `Ŝ`.

The exponent conventions follow the paper: `d ≥ 2`, so the natural-number subtractions
`d-1`, `d-2`, `d-3` in the derivative formulas for `Dfun` are the intended ones (at
`d = 2` the coefficient `d(d-1)(d-2)` vanishes, which is correct since `𝒟''` is then
constant).
-/

namespace UpperTailOptimizers

open Real Filter Topology

/-! ### The scalar entropy `S₀` -/

/-- The paper's `S₀(u) = -½[u log u + (1-u) log(1-u)]`, i.e. half the Shannon entropy.
The project's `bipEnt` is the `S₀`-weighted block sum, which is the paper's `Ŝ`. -/
noncomputable def S0 (u : ℝ) : ℝ := shannonH u / 2

/-- `S₀'(u) = ½ log((1-u)/u)`. -/
noncomputable def dS0 (u : ℝ) : ℝ := (Real.log (1 - u) - Real.log u) / 2

private theorem hasDerivAt_shannonH {u : ℝ} (h0 : u ≠ 0) (h1 : u ≠ 1) :
    HasDerivAt shannonH (Real.log (1 - u) - Real.log u) u := by
  have h : shannonH = Real.binEntropy := funext shannonH_eq_binEntropy
  rw [h]
  exact Real.hasDerivAt_binEntropy h0 h1

theorem hasDerivAt_S0 {u : ℝ} (h0 : u ≠ 0) (h1 : u ≠ 1) : HasDerivAt S0 (dS0 u) u := by
  have := (hasDerivAt_shannonH h0 h1).div_const 2
  exact this

/-- `S₀'' (u) = -1/(2u(1-u)) < 0` — the strict concavity used for the nondegeneracy of the
`a`-direction in paragraph 3. -/
theorem hasDerivAt_dS0 {u : ℝ} (h0 : u ≠ 0) (h1 : u ≠ 1) :
    HasDerivAt dS0 (-1 / (2 * (u * (1 - u)))) u := by
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
    simpa using (hasDerivAt_const u (1:ℝ)).fun_sub (hasDerivAt_id u)
  have h1' : (1:ℝ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hlog1 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - u)) u := by
    simpa [div_eq_mul_inv, Function.comp_def] using (Real.hasDerivAt_log h1').comp u hsub
  have hlog2 : HasDerivAt Real.log (1 / u) u := by
    simpa [one_div] using Real.hasDerivAt_log h0
  have := (hlog1.sub hlog2).div_const 2
  convert this using 1
  all_goals try rfl
  field_simp
  ring

theorem analyticAt_S0 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) : AnalyticAt ℝ S0 u := by
  have h : S0 = fun x => shannonH x / 2 := rfl
  rw [h]
  exact (analyticAt_shannonH h0 h1).div_const

/-- `S₀' ` is real-analytic on `(0,1)`; the companion of `analyticAt_S0`. -/
theorem analyticAt_dS0 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) : AnalyticAt ℝ dS0 u := by
  have h : dS0 = fun x : ℝ => (Real.log (1 - x) - Real.log x) / 2 := rfl
  rw [h]
  have hlog1 : AnalyticAt ℝ (fun x : ℝ => Real.log (1 - x)) u :=
    analyticAt_log_comp (analyticAt_const.sub analyticAt_id) (by linarith)
  have hlog2 : AnalyticAt ℝ (fun x : ℝ => Real.log x) u := analyticAt_log h0
  exact (hlog1.sub hlog2).div_const

/-! ### `𝒩`, `𝒟` and `ψ_d` -/

/-- The paper's `𝒩_ε(z) = 2[S₀(z) - S₀(ε) - S₀'(ε)(z-ε)]` `eq:krrs-entropy-remainder`. -/
noncomputable def Nfun (ε z : ℝ) : ℝ := 2 * (S0 z - S0 ε - dS0 ε * (z - ε))

/-- The paper's `𝒟_ε(z) = z^d - ε^d - d ε^{d-1}(z-ε)` `eq:krrs-moment-remainder`. -/
noncomputable def Dfun (d : ℕ) (ε z : ℝ) : ℝ :=
  z ^ d - ε ^ d - (d : ℝ) * ε ^ (d - 1) * (z - ε)

/-- The paper's `ψ_d(ε,z) = 𝒩_ε(z)/𝒟_ε(z)`, away from `z = ε`. -/
noncomputable def psiD (d : ℕ) (ε z : ℝ) : ℝ := Nfun ε z / Dfun d ε z

/-- `𝒩` in terms of the project's `shannonH`. -/
private theorem Nfun_eq (ε z : ℝ) :
    Nfun ε z = shannonH z - shannonH ε - (Real.log (1 - ε) - Real.log ε) * (z - ε) := by
  unfold Nfun S0 dS0
  ring

/-- `𝒩'_ε(z) = log((1-z)/z) - log((1-ε)/ε)`. -/
noncomputable def dN (ε z : ℝ) : ℝ :=
  Real.log (1 - z) - Real.log z - (Real.log (1 - ε) - Real.log ε)

/-- `𝒩'_ε(z) = 2[S₀'(z) - S₀'(ε)]`: the two normalisations differ by the factor `2`
relating `S₀` to the Shannon entropy. -/
theorem dN_eq_two_mul_dS0 (ε z : ℝ) : dN ε z = 2 * (dS0 z - dS0 ε) := by
  unfold dN dS0
  ring

/-- `𝒩''_ε(z) = -1/(z(1-z))`. -/
noncomputable def d2N (z : ℝ) : ℝ := -1 / (z * (1 - z))

/-- `𝒩'''_ε(z) = (1-2z)/(z²(1-z)²)`. -/
noncomputable def d3N (z : ℝ) : ℝ := (1 - 2 * z) / (z ^ 2 * (1 - z) ^ 2)

theorem hasDerivAt_Nfun (ε : ℝ) {z : ℝ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    HasDerivAt (fun x => Nfun ε x) (dN ε z) z := by
  have hS : HasDerivAt shannonH (Real.log (1 - z) - Real.log z) z := hasDerivAt_shannonH h0 h1
  have hlin : HasDerivAt (fun x : ℝ => (Real.log (1 - ε) - Real.log ε) * (x - ε))
      (Real.log (1 - ε) - Real.log ε) z := by
    simpa using ((hasDerivAt_id z).sub_const ε).const_mul
      (Real.log (1 - ε) - Real.log ε)
  have h := (hS.sub_const (shannonH ε)).sub hlin
  have hfun : (fun x => Nfun ε x)
      = fun x => shannonH x - shannonH ε - (Real.log (1 - ε) - Real.log ε) * (x - ε) :=
    funext fun x => Nfun_eq ε x
  rw [hfun]
  exact h

theorem hasDerivAt_dN (ε : ℝ) {z : ℝ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    HasDerivAt (fun x => dN ε x) (d2N z) z := by
  have h1' : (1:ℝ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h := ((hasDerivAt_dS0 h0 h1).sub_const (dS0 ε)).const_mul (2:ℝ)
  simp only [dN_eq_two_mul_dS0]
  convert h using 1
  all_goals try rfl
  unfold d2N
  field_simp

theorem hasDerivAt_d2N {z : ℝ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    HasDerivAt d2N (d3N z) z := by
  have h1' : (1:ℝ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hden : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * z) z := by
    have h : HasDerivAt (fun x : ℝ => x - x ^ 2) (1 - 2 * z) z := by
      simpa using (hasDerivAt_id z).fun_sub (hasDerivAt_pow 2 z)
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by ring)
  have hne : z * (1 - z) ≠ 0 := mul_ne_zero h0 h1'
  have h := (hden.inv hne).const_mul (-1 : ℝ)
  have hfun : d2N = fun x : ℝ => (-1 : ℝ) * (x * (1 - x))⁻¹ := by
    funext x; unfold d2N; field_simp
  rw [hfun]
  convert h using 1
  all_goals try rfl
  unfold d3N
  field_simp

/-- `𝒟'_ε(z) = d z^{d-1} - d ε^{d-1}`. -/
noncomputable def dD (d : ℕ) (ε z : ℝ) : ℝ :=
  (d : ℝ) * z ^ (d - 1) - (d : ℝ) * ε ^ (d - 1)

/-- `𝒟''_ε(z) = d(d-1) z^{d-2}`. -/
noncomputable def d2D (d : ℕ) (z : ℝ) : ℝ := (d : ℝ) * ((d : ℝ) - 1) * z ^ (d - 2)

/-- `𝒟'''_ε(z) = d(d-1)(d-2) z^{d-3}`. -/
noncomputable def d3D (d : ℕ) (z : ℝ) : ℝ :=
  (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) * z ^ (d - 3)

theorem hasDerivAt_Dfun (d : ℕ) (ε z : ℝ) :
    HasDerivAt (fun x => Dfun d ε x) (dD d ε z) z := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ d) ((d : ℝ) * z ^ (d - 1)) z := by
    simpa using hasDerivAt_pow d z
  have hlin : HasDerivAt (fun x : ℝ => (d : ℝ) * ε ^ (d - 1) * (x - ε))
      ((d : ℝ) * ε ^ (d - 1)) z := by
    simpa using ((hasDerivAt_id z).sub_const ε).const_mul ((d : ℝ) * ε ^ (d - 1))
  have h := (hpow.sub_const (ε ^ d)).sub hlin
  exact h

theorem hasDerivAt_dD {d : ℕ} (hd : 2 ≤ d) (ε z : ℝ) :
    HasDerivAt (fun x => dD d ε x) (d2D d z) z := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (d - 1))
      (((d : ℕ) - 1 : ℕ) * z ^ (d - 1 - 1)) z := by
    simpa using hasDerivAt_pow (d - 1) z
  have h := (hpow.const_mul (d : ℝ)).sub_const ((d : ℝ) * ε ^ (d - 1))
  convert h using 1
  all_goals try rfl
  unfold d2D
  have hcast : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
    have : (1 : ℕ) ≤ d := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast]
  have hexp : d - 1 - 1 = d - 2 := by omega
  rw [hexp]
  ring

theorem hasDerivAt_d2D {d : ℕ} (hd : 2 ≤ d) (z : ℝ) :
    HasDerivAt (fun x => d2D d x) (d3D d z) z := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (d - 2))
      (((d - 2 : ℕ) : ℝ) * z ^ (d - 2 - 1)) z := by
    simpa using hasDerivAt_pow (d - 2) z
  have h := hpow.const_mul ((d : ℝ) * ((d : ℝ) - 1))
  convert h using 1
  all_goals try rfl
  unfold d3D
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · -- `d = 2`: both sides vanish
    have hd2 : d = 2 := by omega
    subst hd2
    norm_num
  · have hcast : (((d - 2 : ℕ) : ℝ)) = (d : ℝ) - 2 := by
      have : (2 : ℕ) ≤ d := hd
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]
    have hexp : d - 2 - 1 = d - 3 := by omega
    rw [hexp]
    ring

/-- Strict convexity of `u ↦ u^d` in the form used in paragraph 2: `𝒟_ε(b) > 0` for
`b ≠ ε`.  This is `pow_convex_gap_pos` of `Nondegeneracy/PowBounds.lean` restated in the
appendix's notation. -/
theorem Dfun_pos {d : ℕ} (hd : 2 ≤ d) {ε z : ℝ} (hε : 0 < ε) (hz : 0 ≤ z) (hne : z ≠ ε) :
    0 < Dfun d ε z := by
  have h := pow_convex_gap_pos hε hz hne hd
  unfold Dfun
  convert h using 1

/-! ### Two elementary block-weight derivatives -/

/-- The derivative of the middle block weight `c ↦ 2c(1-c)`.  Shared by `hasDerivAt_Qmap_c`
and `hasDerivAt_Shat_c_zero` (`KRRS/SCalc.lean`). -/
theorem hasDerivAt_two_mul_one_sub (x : ℝ) :
    HasDerivAt (fun c : ℝ => 2 * c * (1 - c)) (2 - 4 * x) x := by
  have hsub : HasDerivAt (fun c : ℝ => 1 - c) (-1) x := by
    simpa using (hasDerivAt_const x (1:ℝ)).fun_sub (hasDerivAt_id x)
  have hlin : HasDerivAt (fun c : ℝ => 2 * c) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2:ℝ)
  have h := hlin.mul hsub
  convert h using 1
  all_goals try rfl
  ring

/-- The derivative of the second-pode block weight `c ↦ (1-c)²`.  Shared by
`hasDerivAt_Qmap_c` and `hasDerivAt_Shat_c_zero` (`KRRS/SCalc.lean`). -/
theorem hasDerivAt_one_sub_sq (x : ℝ) :
    HasDerivAt (fun c : ℝ => (1 - c) ^ 2) (-2 * (1 - x)) x := by
  have hsub : HasDerivAt (fun c : ℝ => 1 - c) (-1) x := by
    simpa using (hasDerivAt_const x (1:ℝ)).fun_sub (hasDerivAt_id x)
  have h := hsub.pow 2
  convert h using 1
  all_goals try rfl
  push_cast
  ring

/-! ### The edge-density solve `Q` -/

/-- The paper's `Q(ε,a,b,c) = (ε - c²a - 2c(1-c)b)/(1-c)²` `eq:krrs-edge-constraint`: the
unique second-block density giving edge density `ε`. -/
noncomputable def Qmap (ε a b c : ℝ) : ℝ := (ε - c ^ 2 * a - 2 * c * (1 - c) * b) / (1 - c) ^ 2

/-- The defining property of `Q`: the bipodal parameter vector it completes has edge
density exactly `ε`. -/
theorem bipEdge_Qmap {ε a b c : ℝ} (hc : c ≠ 1) :
    bipEdge (a, b, Qmap ε a b c, c) = ε := by
  have h : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  unfold bipEdge Qmap
  field_simp
  ring

@[simp] theorem Qmap_zero (ε a b : ℝ) : Qmap ε a b 0 = ε := by
  unfold Qmap; norm_num

theorem analyticAt_Qmap {p : ℝ × ℝ × ℝ × ℝ} (hc : p.2.2.2 ≠ 1) :
    AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => Qmap w.1 w.2.1 w.2.2.1 w.2.2.2) p := by
  have hcc := analyticAt_fth4 p
  have hden : AnalyticAt ℝ (fun w : ℝ × ℝ × ℝ × ℝ => (1 - w.2.2.2) ^ 2) p :=
    (analyticAt_const.sub hcc).pow 2
  have hne : ((1 : ℝ) - p.2.2.2) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hc))
  exact (((analyticAt_fst4 p).sub ((hcc.pow 2).mul (analyticAt_snd4 p))).sub
    (((analyticAt_const.mul hcc).mul (analyticAt_const.sub hcc)).mul
      (analyticAt_thd4 p))).div hden hne

/-- `∂_c Q|_{c=0} = 2(ε - b)`, the expansion used for `∂_c𝒯̂|_{c=0}`. -/
theorem hasDerivAt_Qmap_c (ε a b : ℝ) :
    HasDerivAt (fun c => Qmap ε a b c) (2 * (ε - b)) 0 := by
  have hnum : HasDerivAt (fun c : ℝ => ε - c ^ 2 * a - 2 * c * (1 - c) * b) (-(2 * b)) 0 := by
    have h1 : HasDerivAt (fun c : ℝ => c ^ 2 * a) 0 (0 : ℝ) := by
      simpa using (hasDerivAt_pow 2 (0:ℝ)).mul_const a
    have h2 : HasDerivAt (fun c : ℝ => 2 * c * (1 - c) * b) (2 * b) (0 : ℝ) := by
      simpa using (hasDerivAt_two_mul_one_sub (0:ℝ)).mul_const b
    simpa using ((hasDerivAt_const (0:ℝ) ε).fun_sub h1).fun_sub h2
  have hden : HasDerivAt (fun c : ℝ => (1 - c) ^ 2) (-2) (0 : ℝ) := by
    simpa using hasDerivAt_one_sub_sq (0:ℝ)
  have hne : ((1 : ℝ) - (0:ℝ)) ^ 2 ≠ 0 := by norm_num
  have h := hnum.div hden hne
  have hQ : (fun c => Qmap ε a b c)
      = fun c : ℝ => (ε - c ^ 2 * a - 2 * c * (1 - c) * b) / (1 - c) ^ 2 := rfl
  rw [hQ]
  convert h using 1
  all_goals try rfl
  ring

/-! ### The edge-constrained `H`-density and entropy -/

/-- The paper's `𝒯̂(ε,a,b,c) = t(H, G(a,b,Q(ε,a,b,c),c))`. -/
noncomputable def That {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (ε a b c : ℝ) : ℝ := tBip H a b (Qmap ε a b c) c

/-- The paper's `Ŝ(ε,a,b,c) = c²S₀(a) + 2c(1-c)S₀(b) + (1-c)²S₀(Q(ε,a,b,c))`. -/
noncomputable def Shat (ε a b c : ℝ) : ℝ :=
  c ^ 2 * S0 a + 2 * c * (1 - c) * S0 b + (1 - c) ^ 2 * S0 (Qmap ε a b c)

/-- `Ŝ` is the block entropy of the completed parameter vector: the chart of
`KRRS/Chart.lean` and the appendix's `Ŝ` agree. -/
theorem Shat_eq_bipEnt (ε a b c : ℝ) :
    Shat ε a b c = bipEnt (a, b, Qmap ε a b c, c) := by
  unfold Shat bipEnt S0
  ring

/-- `𝒯̂` is the `H`-density of the completed parameter vector. -/
theorem That_eq_bipTd {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (ε a b c : ℝ) :
    That H ε a b c = bipTd H (a, b, Qmap ε a b c, c) := rfl

@[simp] theorem That_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (ε a b : ℝ) :
    That H ε a b 0 = ε ^ H.edgeFinset.card := by
  unfold That
  rw [Qmap_zero, tBip_zero]

@[simp] theorem Shat_zero (ε a b : ℝ) : Shat ε a b 0 = S0 ε := by
  unfold Shat
  rw [Qmap_zero]
  ring

end UpperTailOptimizers
