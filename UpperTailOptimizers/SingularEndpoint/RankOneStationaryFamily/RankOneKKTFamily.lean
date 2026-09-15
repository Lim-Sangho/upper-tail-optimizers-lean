import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.StationaryBipodality
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyUnique
import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.MuExpansion
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.FamilyContinuity
import UpperTailOptimizers.SingularEndpoint.Proof.Terminal
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.RowSign
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Forced

/-!
# `lem:rank-one-kkt-family` in the paper's form

`KKTFamily d` (`SingularEndpoint/RankOneStationaryFamily/Family.lean`) stores the analytic family
`h ↦ (u_h, p_h, γ_h, α_h)` of `lem:rank-one-kkt-family` of
`paper/sections/singular_stationary_family.tex` together with its *scalar* content: the three
equations `eq:three-value-kkt` in the form `F_{p_h,γ_h} = 0` and the block balance.  The lemma
itself says more, and this file proves the rest, collected in `rank_one_kkt_family`:

* **the variational conditions.**  For `|h| < h₀`, `W_h` satisfies the KKT conditions at
  `(p_h, r_h)` with multiplier `μ_h` (`SatisfiesKKT`, i.e. `eq:graphon-stationarity`, `μ_h ≥ 0`
  and `t(H,W_h) = r_h^m`) and `eq:block-stationarity` (`IsBlockStationary`):
  `KKTFamily.satisfiesKKT_graphon`, `KKTFamily.isBlockStationary_graphon`;
* **admissibility on one window.**  `0 < p_h < r_h < 1`, `s_h, t_h, α_h ∈ (0,1)`, `μ_h > 0`, and
  real-analyticity of `q_h, r_h, μ_h` for `|h| < h₀`: `KKTFamily.exists_window_p_lt_rVal`,
  `KKTFamily.muVal_pos_of_gam_pos`, `KKTFamily.analyticAt_muVal_of_mem`;
* **the converse (local exhaustiveness).**  A nearby nonconstant rank-one graphon `f ⊗ f` with
  factor bounded away from `0` and `1`, satisfying the KKT conditions and
  `eq:block-stationarity`, is a relabelling of a unique `W_h` with `h ∈ (0, h₀)`, and all its
  parameters are the family's: `KKTFamily.exists_converse_rankOne`, with the normalised form
  `KKTFamily.exists_converse_blockGraphon`.

The window `h₀` depends on `d` only (`rmk:rank-one-family-universality`): it is chosen before
the graph `H`.  Only the radius `ε` of the converse depends on `H`, through the base value
`μ_* = 1/(m r_*^m)` of the multiplier.

## Proof of the converse

`kkt_scalar_of_stationary` turns the KKT conditions into `eq:rank-one-kkt` almost everywhere;
the three block cells of `W_{α,s,t}` have positive measure, so `F_{p,γ}` vanishes at `s²`, `st`,
`t²` (`three_values_of_ae`), with `γ = μ m q^{v-2}`.  `exists_scalar_family_locally_unique` is the
uniqueness half of the implicit function theorem for these equations; the family `B` is
continuous at `0` and solves the same equations, so it lies on the implicit-function curve for
small `h` (`KKTFamily.exists_scalar_converse`).  Hence `(u, ℓ(p), γ) = (u_h, ℓ(p_h), γ_h)` at
`h = (t-s)/2`; injectivity of `ℓ` gives `p = p_h`; the block balance, whose coefficient does not
vanish, gives `α = α_h` (`rowBalance_weight_unique`); `t(H,W) = q^v = r^m` gives `r = r_h`; and
`γ = μ m q^{v-2}` gives `μ = μ_h`.  For a general factor the normal form comes from
`lem:stationary-rank-one-bipodality` (`stationary_rank_one_bipodality`), and everything is
transported along the relabelling.  Uniqueness of the index holds because the largest and
smallest values `t_h²`, `s_h²` of `W_h` are relabelling invariants
(`KKTFamily.eq_of_integral_comp_eq`).

## Contents

* `two_le_card_of_edge`, `muVal_exponent_eq` — graph bookkeeping for `μ_h`;
* `integral_ite_pow`, `indicator_factor_eq_ite`, `bipodalValue_Icc_eq_ite`,
  `three_values_of_ae` — the two-valued factor `f_{α,s,t}`;
* `rowBalance_weight_unique`, `continuousAt_ell_pStar` — two scalar facts;
* `KKTFamily.muVal_eq_div_pow`, `.muVal_mul_eq_gam`, `.analyticAt_muVal_of_mem`,
  `.muVal_pos_of_gam_pos` — the multiplier `μ_h = γ_h/(m q_h^{v-2})`;
* `KKTFamily.three_value_kkt` — `eq:three-value-kkt` in the paper's form;
* `KKTFamily.graphon_toFun_eq_factor` — `W_h = f_h ⊗ f_h`;
* `KKTFamily.satisfiesKKT_graphon`, `.isBlockStationary_graphon` — the variational conditions;
* `KKTFamily.exists_window_p_lt_rVal` — `p_h < r_h` and `γ_h > 0` near `0`;
* `KKTFamily.eq_of_integral_comp_eq` — distinct members are not relabellings of each other;
* `KKTFamily.exists_scalar_converse`, `.muStar_mul_eq_gammaStar`,
  `.exists_converse_of_scalar`, `.exists_converse_blockGraphon`, `.exists_converse_rankOne` —
  local exhaustiveness;
* **`rank_one_kkt_family`** — `lem:rank-one-kkt-family`.
-/

namespace UpperTailOptimizers

open MeasureTheory Filter Topology

universe u

variable {d : ℕ}

/-! ## Graph bookkeeping -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

omit [DecidableEq V] in
/-- A graph with an edge has at least two vertices. -/
theorem two_le_card_of_edge (hcard : 1 ≤ H.edgeFinset.card) : 2 ≤ Fintype.card V := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp hcard
  induction e using Sym2.ind with
  | _ a b =>
    have hadj : H.Adj a b := by
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨a, b, hadj.ne⟩

/-- For a `d`-regular `H` with an edge, the real exponent `2m/d - 2` of `KKTFamily.muVal` is the
natural number `v - 2`. -/
theorem muVal_exponent_eq (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) :
    2 * (H.edgeFinset.card : ℝ) / (d : ℝ) - 2 = ((Fintype.card V - 2 : ℕ) : ℝ) := by
  have hv2 := two_le_card_of_edge H hcard
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
  have hhand : (Fintype.card V : ℝ) * (d : ℝ) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast regular_handshake H hreg
  rw [Nat.cast_sub hv2, ← hhand]
  field_simp
  push_cast
  ring

end Graph

/-! ## Two-valued factors -/

/-- `∫ g^k = α s^k + (1-α) t^k` for the everywhere-defined two-valued factor
`g = s` on `[0,α]`, `g = t` off it. -/
theorem integral_ite_pow {α s t : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    ∫ x, (if x ∈ Set.Icc (0:ℝ) α then s else t) ^ k ∂unitμ = α * s ^ k + (1 - α) * t ^ k := by
  classical
  have hfun : (fun x : ℝ => (if x ∈ Set.Icc (0:ℝ) α then s else t) ^ k)
      = fun x => (Set.Icc (0:ℝ) α).indicator (fun _ => s ^ k) x
          + (Set.Icc (0:ℝ) α)ᶜ.indicator (fun _ => t ^ k) x := by
    funext x
    by_cases hx : x ∈ Set.Icc (0:ℝ) α
    · simp [hx]
    · simp [hx]
  have hA : MeasurableSet (Set.Icc (0:ℝ) α) := measurableSet_Icc
  rw [hfun, integral_add ((integrable_const _).indicator hA)
    ((integrable_const _).indicator hA.compl), integral_indicator_const _ hA,
    integral_indicator_const _ hA.compl, measureReal_compl hA]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, unitμ_Icc_toReal hα0 hα1,
    smul_eq_mul]

/-- The paper's factor `f_{α,s,t} = s 1_{[0,α]} + t 1_{(α,1]}` agrees on `[0,1]` with the
everywhere-defined two-valued factor. -/
theorem indicator_factor_eq_ite {α s t x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (Set.Icc 0 α).indicator (fun _ => s) x + (Set.Ioc α 1).indicator (fun _ => t) x
      = if x ∈ Set.Icc (0:ℝ) α then s else t := by
  classical
  by_cases h : x ≤ α
  · have h1 : x ∈ Set.Icc (0:ℝ) α := ⟨hx.1, h⟩
    have h2 : x ∉ Set.Ioc α 1 := fun h' => absurd h (not_le.mpr h'.1)
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, if_pos h1, add_zero]
  · have h1 : x ∉ Set.Icc (0:ℝ) α := fun h' => h h'.2
    have h2 : x ∈ Set.Ioc α 1 := ⟨lt_of_not_ge h, hx.2⟩
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, if_neg h1, zero_add]

/-- The two-block rank-one graphon is `g ⊗ g` for the everywhere-defined two-valued factor. -/
theorem bipodalValue_Icc_eq_ite (α s t x y : ℝ) :
    bipodalValue (Set.Icc 0 α) (s ^ 2) (s * t) (t ^ 2) (x, y)
      = (if x ∈ Set.Icc (0:ℝ) α then s else t) * (if y ∈ Set.Icc (0:ℝ) α then s else t) := by
  classical
  unfold bipodalValue
  by_cases hx : x ∈ Set.Icc (0:ℝ) α <;> by_cases hy : y ∈ Set.Icc (0:ℝ) α <;>
    simp only [hx, hy, if_true, if_false] <;> ring

/-- **Reading the three values off an almost-everywhere identity.**  If `g = s` on `(0,α)` and
`g = t` on `(α,1)` with `0 < α < 1`, a property of `g(x)g(y)` holding for `gμ`-a.e. `(x,y)`
holds at `s·s`, `s·t` and `t·t`: each is the value on a cell of positive measure. -/
theorem three_values_of_ae {P : ℝ → Prop} {g : ℝ → ℝ} {α s t : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hs : ∀ x ∈ Set.Ioo (0:ℝ) α, g x = s) (ht : ∀ x ∈ Set.Ioo α 1, g x = t)
    (hae : ∀ᵐ z ∂gμ, P (g z.1 * g z.2)) : P (s * s) ∧ P (s * t) ∧ P (t * t) := by
  have hpos : ∀ a b : ℝ, a < b → 0 ≤ a → b ≤ 1 → unitμ (Set.Ioo a b) ≠ 0 := by
    intro a b hab ha hb
    have hsub : Set.Ioo a b ⊆ Set.Icc (0:ℝ) 1 := fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [unitμ, Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub,
      Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hnull := ae_iff.mp hae
  have key : ∀ (A C : Set ℝ) (a c : ℝ), unitμ A ≠ 0 → unitμ C ≠ 0 → (∀ x ∈ A, g x = a) →
      (∀ y ∈ C, g y = c) → P (a * c) := by
    intro A C a c hA hC ha hc
    by_contra hP
    have hsub : A ×ˢ C ⊆ {z : ℝ × ℝ | ¬ P (g z.1 * g z.2)} := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      show ¬ P (g x * g y)
      rw [ha x hx, hc y hy]
      exact hP
    have h0 := measure_mono_null hsub hnull
    rw [show gμ = unitμ.prod unitμ from rfl, Measure.prod_prod] at h0
    exact (mul_ne_zero hA hC) h0
  have h1 := hpos 0 α hα0 le_rfl hα1.le
  have h2 := hpos α 1 hα1 hα0.le le_rfl
  exact ⟨key _ _ _ _ h1 h1 hs hs, key _ _ _ _ h1 h2 hs ht, key _ _ _ _ h2 h2 ht ht⟩

/-- **The block weight is determined by `eq:block-proportion-balance`.**  The linear equation
`α(𝓜(z₁) - 𝓜(z₂)) = (1-α)(𝓜(z₃) - 𝓜(z₂))` has at most one solution, because the coefficient
`(𝓜(z₁) - 𝓜(z₂)) + (𝓜(z₃) - 𝓜(z₂))` does not vanish (`rowBalance_denom_ne_zero`). -/
theorem rowBalance_weight_unique (hd : 2 ≤ d) {p γ z₁ z₂ z₃ a b : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃ : z₃ < 1)
    (e₁ : Fkkt d p γ z₁ = 0) (e₂ : Fkkt d p γ z₂ = 0) (e₃ : Fkkt d p γ z₃ = 0)
    (ha : a * (Mfun d p γ z₁ - Mfun d p γ z₂) = (1 - a) * (Mfun d p γ z₃ - Mfun d p γ z₂))
    (hb : b * (Mfun d p γ z₁ - Mfun d p γ z₂) = (1 - b) * (Mfun d p γ z₃ - Mfun d p γ z₂)) :
    a = b := by
  have hne := rowBalance_denom_ne_zero hd hp0 hp1 h₁ h₁₂ h₂₃ h₃ e₁ e₂ e₃
  have hz : (a - b) * ((Mfun d p γ z₁ - Mfun d p γ z₂) + (Mfun d p γ z₃ - Mfun d p γ z₂)) = 0 := by
    linear_combination ha - hb
  rcases mul_eq_zero.mp hz with h | h
  · linarith
  · exact absurd h hne

/-- The log-odds `ℓ` is continuous at `p_*`. -/
theorem continuousAt_ell_pStar (hd : 2 ≤ d) : ContinuousAt ell (pStar d) := by
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  have hdiv : ContinuousAt (fun z : ℝ => (1 - z) / z) (pStar d) :=
    (continuousAt_const.sub continuousAt_id).div continuousAt_id (ne_of_gt hp0)
  exact hdiv.log (div_pos (by linarith) hp0).ne'

/-! ## The family on its window -/

namespace KKTFamily

variable {B : KKTFamily d}

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- **`μ_h = γ_h/(m q_h^{v-2})`** with the natural-number exponent `v - 2` of
`lem:rank-one-kkt-family`; `KKTFamily.muVal` writes the exponent as the real number
`2m/d - 2`. -/
theorem muVal_eq_div_pow (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) (h : ℝ) :
    B.muVal (H.edgeFinset.card : ℝ) h
      = B.gam h / ((H.edgeFinset.card : ℝ) * B.qVal h ^ (Fintype.card V - 2)) := by
  rw [muVal, muVal_exponent_eq H hd hreg hcard, Real.rpow_natCast]

/-- The defining relation `γ_h = μ_h m q_h^{v-2}` of the multiplier. -/
theorem muVal_mul_eq_gam (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) {h : ℝ} (hh : |h| < B.h₀) :
    B.muVal (H.edgeFinset.card : ℝ) h * (H.edgeFinset.card : ℝ)
        * B.qVal h ^ (Fintype.card V - 2) = B.gam h := by
  rw [muVal_eq_div_pow H hd hreg hcard]
  have hq : 0 < B.qVal h ^ (Fintype.card V - 2) := pow_pos (qVal_pos hh) _
  have hm : (0 : ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hcard
  field_simp

end Graph

/-- `μ_h` is real-analytic at every point of the window (`analyticAt_muVal` is the case
`h = 0`). -/
theorem analyticAt_muVal_of_mem {m : ℝ} (hm : 0 < m) {h : ℝ} (hh : |h| < B.h₀) :
    AnalyticAt ℝ (B.muVal m) h := by
  have hq0 : 0 < B.qVal h := qVal_pos hh
  have hpow : AnalyticAt ℝ (fun z : ℝ => B.qVal z ^ (2 * m / (d : ℝ) - 2)) h := by
    have hexp : AnalyticAt ℝ
        (fun z : ℝ => Real.exp (Real.log (B.qVal z) * (2 * m / (d : ℝ) - 2))) h :=
      (((analyticAt_qVal hh).log hq0).mul analyticAt_const).rexp'
    refine hexp.congr ?_
    filter_upwards [eventually_window_of_mem hh] with z hz
    exact (Real.rpow_def_of_pos (qVal_pos hz) _).symm
  have hden0 : m * B.qVal h ^ (2 * m / (d : ℝ) - 2) ≠ 0 :=
    (mul_pos hm (Real.rpow_pos_of_pos hq0 _)).ne'
  exact (B.analyticAt_gam h hh).div (analyticAt_const.mul hpow) hden0

/-- `μ_h > 0` wherever `γ_h > 0`. -/
theorem muVal_pos_of_gam_pos {m : ℝ} (hm : 0 < m) {h : ℝ} (hh : |h| < B.h₀)
    (hg : 0 < B.gam h) : 0 < B.muVal m h :=
  div_pos hg (mul_pos hm (Real.rpow_pos_of_pos (qVal_pos hh) _))

/-- **`eq:three-value-kkt`** along the family, in the paper's form
`ℓ(p) - ℓ(s²) = γ s^{2d-2}`, `ℓ(p) - ℓ(st) = γ (st)^{d-1}`, `ℓ(p) - ℓ(t²) = γ t^{2d-2}`. -/
theorem three_value_kkt {h : ℝ} (hh : |h| < B.h₀) :
    ell (B.p h) - ell (B.sVal h ^ 2) = B.gam h * B.sVal h ^ (2 * d - 2) ∧
      ell (B.p h) - ell (B.sVal h * B.tVal h) = B.gam h * (B.sVal h * B.tVal h) ^ (d - 1) ∧
      ell (B.p h) - ell (B.tVal h ^ 2) = B.gam h * B.tVal h ^ (2 * d - 2) := by
  have hp := B.p_mem h hh
  have hs0 := sVal_pos hh
  have hs1 := sVal_lt_one hh
  have ht0 := tVal_pos hh
  have ht1 := tVal_lt_one hh
  have e1 : Fkkt d (B.p h) (B.gam h) (B.sVal h ^ 2) = 0 := B.kkt_ss h hh
  have e2 : Fkkt d (B.p h) (B.gam h) (B.sVal h * B.tVal h) = 0 := B.kkt_st h hh
  have e3 : Fkkt d (B.p h) (B.gam h) (B.tVal h ^ 2) = 0 := B.kkt_tt h hh
  have hpow : ∀ x : ℝ, (x ^ 2) ^ (d - 1) = x ^ (2 * d - 2) := fun x => by
    rw [← pow_mul]; congr 1; omega
  rw [Fkkt, Jp'_eq_ell_sub hp.1 hp.2 (by positivity) (by nlinarith)] at e1 e3
  rw [Fkkt, Jp'_eq_ell_sub hp.1 hp.2 (by positivity) (by nlinarith)] at e2
  rw [← hpow, ← hpow]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **`W_h = f_h ⊗ f_h`** on `[0,1]²`, with the paper's factor
`f_h = f_{α_h,s_h,t_h} = s_h 1_{[0,α_h]} + t_h 1_{(α_h,1]}`. -/
theorem graphon_toFun_eq_factor {h : ℝ} (hh : |h| < B.h₀) {x y : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    (B.graphon hh).toFun x y
      = ((Set.Icc 0 (B.alph h)).indicator (fun _ => B.sVal h) x
          + (Set.Ioc (B.alph h) 1).indicator (fun _ => B.tVal h) x)
        * ((Set.Icc 0 (B.alph h)).indicator (fun _ => B.sVal h) y
          + (Set.Ioc (B.alph h) 1).indicator (fun _ => B.tVal h) y) := by
  rw [indicator_factor_eq_ite hx, indicator_factor_eq_ite hy]
  exact bipodalValue_Icc_eq_ite _ _ _ x y

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- **`W_h` satisfies the KKT conditions at `(p_h, r_h)` with multiplier `μ_h`**
(`lem:rank-one-kkt-family`), wherever `γ_h ≥ 0`.  The three scalar equations
`eq:three-value-kkt` give `eq:rank-one-kkt` at every point, and
`isStationary_of_kkt_scalar` turns that into `eq:graphon-stationarity`. -/
theorem satisfiesKKT_graphon (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) {h : ℝ} (hh : |h| < B.h₀) (hg : 0 ≤ B.gam h) :
    SatisfiesKKT H (B.p h) (B.rVal h) (B.muVal (H.edgeFinset.card : ℝ) h) (B.graphon hh) := by
  classical
  have hm : (0 : ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hcard
  have hμ : 0 ≤ B.muVal (H.edgeFinset.card : ℝ) h :=
    div_nonneg hg (mul_pos hm (Real.rpow_pos_of_pos (qVal_pos hh) _)).le
  refine ⟨hμ, graphon_tDensity_eq_rVal_pow H hd hreg hh, ?_⟩
  have hp := B.p_mem h hh
  have ha := B.alph_mem h hh
  have hs0 := sVal_pos hh
  have hs1 := sVal_lt_one hh
  have ht0 := tVal_pos hh
  have ht1 := tVal_lt_one hh
  set g : ℝ → ℝ := fun x => if x ∈ Set.Icc (0:ℝ) (B.alph h) then B.sVal h else B.tVal h
    with hgdef
  set η : ℝ := min (min (B.sVal h) (B.tVal h)) (min (1 - B.sVal h) (1 - B.tVal h)) with hηdef
  have hη : 0 < η := lt_min (lt_min hs0 ht0) (lt_min (by linarith) (by linarith))
  have hg0 : ∀ y, η ≤ g y := by
    intro y
    by_cases hy : y ∈ Set.Icc (0:ℝ) (B.alph h)
    · simp only [hgdef, if_pos hy]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    · simp only [hgdef, if_neg hy]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hg1 : ∀ y, g y ≤ 1 - η := by
    intro y
    have h1 : η ≤ 1 - B.sVal h := le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : η ≤ 1 - B.tVal h := le_trans (min_le_right _ _) (min_le_right _ _)
    by_cases hy : y ∈ Set.Icc (0:ℝ) (B.alph h)
    · simp only [hgdef, if_pos hy]; linarith
    · simp only [hgdef, if_neg hy]; linarith
  have hgm : Measurable g := measurable_const.ite measurableSet_Icc measurable_const
  have hint : ∫ y, g y ^ d ∂unitμ = B.qVal h := integral_ite_pow ha.1.le ha.2.le d
  have hscalar : ∀ᵐ z ∂gμ, Fkkt d (B.p h)
      (B.muVal (H.edgeFinset.card : ℝ) h * (H.edgeFinset.card : ℝ)
        * (∫ y, g y ^ d ∂unitμ) ^ (Fintype.card V - 2)) (g z.1 * g z.2) = 0 := by
    rw [hint, muVal_mul_eq_gam H hd hreg hcard hh]
    refine Eventually.of_forall fun z => ?_
    have e1 : Fkkt d (B.p h) (B.gam h) (B.sVal h * B.sVal h) = 0 := by
      rw [← sq]; exact B.kkt_ss h hh
    have e2 : Fkkt d (B.p h) (B.gam h) (B.sVal h * B.tVal h) = 0 := B.kkt_st h hh
    have e2' : Fkkt d (B.p h) (B.gam h) (B.tVal h * B.sVal h) = 0 := by
      rw [mul_comm]; exact e2
    have e3 : Fkkt d (B.p h) (B.gam h) (B.tVal h * B.tVal h) = 0 := by
      rw [← sq]; exact B.kkt_tt h hh
    by_cases h1 : z.1 ∈ Set.Icc (0:ℝ) (B.alph h) <;>
      by_cases h2 : z.2 ∈ Set.Icc (0:ℝ) (B.alph h) <;>
      simp only [hgdef, h1, h2, if_true, if_false] <;> assumption
  have hstat := isStationary_of_kkt_scalar H hreg hp.1 hp.2 hη hgm hg0 hg1 hscalar
  refine isStationary_congr_ae H (Eventually.of_forall fun z => ?_) hstat
  show g z.1 * g z.2 = bipodalValue (Set.Icc 0 (B.alph h)) (B.sVal h ^ 2)
    (B.sVal h * B.tVal h) (B.tVal h ^ 2) (z.1, z.2)
  rw [bipodalValue_Icc_eq_ite]

/-- **`W_h` satisfies `eq:block-stationarity`** (`lem:rank-one-kkt-family`): by
`blockStationary_iff_rowBalance`, with `γ = μ_h m q_h^{v-2} = γ_h`, it is the block balance
`KKTFamily.rowBalance`. -/
theorem isBlockStationary_graphon (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) {h : ℝ} (hh : |h| < B.h₀) :
    IsBlockStationary H (B.p h) (B.muVal (H.edgeFinset.card : ℝ) h)
      (sq_sVal_mem hh) (cross_mem hh) (sq_tVal_mem hh) (B.alph h) := by
  have hp := B.p_mem h hh
  have ha := B.alph_mem h hh
  rw [blockStationary_iff_rowBalance H hreg hcard hp.1 hp.2 _ _ _ ha.1 ha.2]
  have hq : B.alph h * B.sVal h ^ d + (1 - B.alph h) * B.tVal h ^ d = B.qVal h := rfl
  rw [hq, muVal_mul_eq_gam H hd hreg hcard hh]
  exact B.rowBalance h hh

end Graph

/-- **The ordering `p_h < r_h` and the sign `γ_h > 0` near `h = 0`**: both hold at `h = 0`
(`p_* < r_*`, `γ_* > 0`) and persist by continuity. -/
theorem exists_window_p_lt_rVal (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → B.p h < B.rVal h ∧ 0 < B.gam h := by
  have hmid := pStar_lt_rStar hd
  have e1 : ∀ᶠ h in 𝓝 (0:ℝ), B.p h < (pStar d + rStar d) / 2 :=
    (tendsto_p B).eventually_lt_const (by linarith)
  have e2 : ∀ᶠ h in 𝓝 (0:ℝ), (pStar d + rStar d) / 2 < B.rVal h := by
    have hr := (analyticAt_rVal (zero_mem_window B)).continuousAt.tendsto
    rw [rVal_zero hd B] at hr
    exact hr.eventually_const_lt (by linarith)
  have e3 : ∀ᶠ h in 𝓝 (0:ℝ), 0 < B.gam h :=
    (tendsto_gam_nhds B).eventually_const_lt (gammaStar_pos hd)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and (e2.and e3))
  refine ⟨δ, hδ, fun h hh => ?_⟩
  have hx := hball (by rwa [Real.dist_eq, sub_zero])
  exact ⟨lt_trans hx.1 hx.2.1, hx.2.2⟩

/-! ### Uniqueness of the index -/

/-- **Distinct members of the family are not relabellings of each other.**  If every integral
`∬ φ(W)` of a measurable `φ` takes the same value on `W_h` and `W_{h'}` with `h, h' > 0` — as it
does when the two are measure-preserving relabellings of each other — then `h = h'`.

Testing against `φ = 1_{(c,∞)}` and `φ = 1_{(-∞,c)}` identifies the largest value `t_h²` and
the smallest value `s_h²` of `W_h`, each carried by a block cell of positive measure; and
`t_h - s_h = 2h`. -/
theorem eq_of_integral_comp_eq {h h' : ℝ} (hh : |h| < B.h₀) (hh' : |h'| < B.h₀)
    (hpos : 0 < h) (hpos' : 0 < h')
    (heq : ∀ φ : ℝ → ℝ, Measurable φ →
      ∫ z, φ ((B.graphon hh).toFun z.1 z.2) ∂gμ = ∫ z, φ ((B.graphon hh').toFun z.1 z.2) ∂gμ) :
    h = h' := by
  classical
  -- the block form of `∬ φ(W_h)`
  have hform : ∀ (k : ℝ) (hk : |k| < B.h₀) (φ : ℝ → ℝ),
      ∫ z, φ ((B.graphon hk).toFun z.1 z.2) ∂gμ
        = φ (B.sVal k ^ 2) * B.alph k ^ 2
          + φ (B.sVal k * B.tVal k) * (2 * B.alph k * (1 - B.alph k))
          + φ (B.tVal k ^ 2) * (1 - B.alph k) ^ 2 := by
    intro k hk φ
    have ha := B.alph_mem k hk
    rw [graphon, bipodalGraphon_integral_comp, unitμ_Icc_toReal ha.1.le ha.2.le]
  -- the top value
  have htop : ∀ (k k' : ℝ) (hk : |k| < B.h₀) (hk' : |k'| < B.h₀), 0 < k' →
      (∀ φ : ℝ → ℝ, Measurable φ →
        ∫ z, φ ((B.graphon hk).toFun z.1 z.2) ∂gμ
          = ∫ z, φ ((B.graphon hk').toFun z.1 z.2) ∂gμ) →
      B.tVal k ^ 2 ≤ B.tVal k' ^ 2 := by
    intro k k' hk hk' hk'0 hφ
    by_contra hlt
    push Not at hlt
    set φ : ℝ → ℝ := (Set.Ioi (B.tVal k' ^ 2)).indicator 1 with hφdef
    have hφm : Measurable φ := measurable_one.indicator measurableSet_Ioi
    have hst' := B.sVal_lt_tVal hk'0
    have hs' := sVal_pos hk'
    have hz1 : φ (B.sVal k' ^ 2) = 0 :=
      Set.indicator_of_notMem (fun h => absurd h (not_lt.mpr (by nlinarith))) _
    have hz2 : φ (B.sVal k' * B.tVal k') = 0 :=
      Set.indicator_of_notMem (fun h => absurd h (not_lt.mpr (by nlinarith))) _
    have hz3 : φ (B.tVal k' ^ 2) = 0 :=
      Set.indicator_of_notMem (fun h => absurd h (lt_irrefl _)) _
    have hone : φ (B.tVal k ^ 2) = 1 := by
      rw [hφdef, Set.indicator_of_mem (show B.tVal k ^ 2 ∈ Set.Ioi (B.tVal k' ^ 2) from hlt)]
      rfl
    have hnn : ∀ x, 0 ≤ φ x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have e := hφ φ hφm
    rw [hform k hk, hform k' hk', hz1, hz2, hz3, hone] at e
    have ha := B.alph_mem k hk
    have h1 : 0 ≤ φ (B.sVal k ^ 2) * B.alph k ^ 2 := mul_nonneg (hnn _) (sq_nonneg _)
    have h2 : 0 ≤ φ (B.sVal k * B.tVal k) * (2 * B.alph k * (1 - B.alph k)) :=
      mul_nonneg (hnn _) (by nlinarith [ha.1, ha.2])
    have h3 : 0 < (1 - B.alph k) ^ 2 := by nlinarith [ha.2]
    linarith
  -- the bottom value
  have hbot : ∀ (k k' : ℝ) (hk : |k| < B.h₀) (hk' : |k'| < B.h₀), 0 < k' →
      (∀ φ : ℝ → ℝ, Measurable φ →
        ∫ z, φ ((B.graphon hk).toFun z.1 z.2) ∂gμ
          = ∫ z, φ ((B.graphon hk').toFun z.1 z.2) ∂gμ) →
      B.sVal k' ^ 2 ≤ B.sVal k ^ 2 := by
    intro k k' hk hk' hk'0 hφ
    by_contra hlt
    push Not at hlt
    set φ : ℝ → ℝ := (Set.Iio (B.sVal k' ^ 2)).indicator 1 with hφdef
    have hφm : Measurable φ := measurable_one.indicator measurableSet_Iio
    have hst' := B.sVal_lt_tVal hk'0
    have hs' := sVal_pos hk'
    have hz1 : φ (B.sVal k' ^ 2) = 0 := by
      rw [hφdef]; exact Set.indicator_of_notMem (by simp only [Set.mem_Iio, not_lt]; rfl) _
    have hz2 : φ (B.sVal k' * B.tVal k') = 0 := by
      rw [hφdef]; exact Set.indicator_of_notMem (by simp only [Set.mem_Iio, not_lt]; nlinarith) _
    have hz3 : φ (B.tVal k' ^ 2) = 0 := by
      rw [hφdef]; exact Set.indicator_of_notMem (by simp only [Set.mem_Iio, not_lt]; nlinarith) _
    have hone : φ (B.sVal k ^ 2) = 1 := by
      rw [hφdef, Set.indicator_of_mem (show B.sVal k ^ 2 ∈ Set.Iio (B.sVal k' ^ 2) from hlt)]
      rfl
    have hnn : ∀ x, 0 ≤ φ x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have e := hφ φ hφm
    rw [hform k hk, hform k' hk', hz1, hz2, hz3, hone] at e
    have ha := B.alph_mem k hk
    have h2 : 0 ≤ φ (B.sVal k * B.tVal k) * (2 * B.alph k * (1 - B.alph k)) :=
      mul_nonneg (hnn _) (by nlinarith [ha.1, ha.2])
    have h3 : 0 ≤ φ (B.tVal k ^ 2) * (1 - B.alph k) ^ 2 := mul_nonneg (hnn _) (sq_nonneg _)
    have h1 : 0 < B.alph k ^ 2 := by nlinarith [ha.1]
    linarith
  have heq' : ∀ φ : ℝ → ℝ, Measurable φ →
      ∫ z, φ ((B.graphon hh').toFun z.1 z.2) ∂gμ = ∫ z, φ ((B.graphon hh).toFun z.1 z.2) ∂gμ :=
    fun φ hφ => (heq φ hφ).symm
  have ht : B.tVal h = B.tVal h' :=
    (sq_eq_sq₀ (tVal_pos hh).le (tVal_pos hh').le).mp
      (le_antisymm (htop h h' hh hh' hpos' heq) (htop h' h hh' hh hpos heq'))
  have hs : B.sVal h = B.sVal h' :=
    (sq_eq_sq₀ (sVal_pos hh).le (sVal_pos hh').le).mp
      (le_antisymm (hbot h' h hh' hh hpos heq') (hbot h h' hh hh' hpos' heq))
  have e1 : B.tVal h - B.sVal h = 2 * h := by simp only [tVal, sVal]; ring
  have e2 : B.tVal h' - B.sVal h' = 2 * h' := by simp only [tVal, sVal]; ring
  rw [ht, hs] at e1
  linarith

/-! ### Local exhaustiveness in scalar coordinates -/

/-- **The scalar converse for the family itself.**  `exists_scalar_family_locally_unique` pins a
nearby solution of `eq:three-value-kkt` to the implicit-function curve `z`; the family `B`,
being continuous at `0` and solving the same equations, lies on that curve for small `h`.  So a
nearby solution `(u, ℓ, γ)` at half-gap `h ∈ (0, h₁)` is `(u_h, ℓ(p_h), γ_h)`.  The radii depend
on `d` only. -/
theorem exists_scalar_converse (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ ≤ B.h₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ h : ℝ, 0 < h → h < h₁ → ∀ u lv g : ℝ,
        |u - uStar d| < ε₁ → |lv - ellStar d| < ε₁ → |g - gammaStar d| < ε₁ →
        0 < u - h → u + h < 1 →
        Lell d lv g ((u - h) ^ 2) = 0 → Lell d lv g ((u - h) * (u + h)) = 0 →
        Lell d lv g ((u + h) ^ 2) = 0 →
        u = B.u h ∧ lv = ell (B.p h) ∧ g = B.gam h := by
  obtain ⟨h0, ε, z, hh0, hε, -, -, -, huniq⟩ := exists_scalar_family_locally_unique hd
  have e1 : ∀ᶠ h in 𝓝 (0:ℝ), |B.u h - uStar d| < ε := by
    have := Metric.tendsto_nhds.mp (tendsto_u_nhds B) ε hε
    simpa [Real.dist_eq] using this
  have e2 : ∀ᶠ h in 𝓝 (0:ℝ), |ell (B.p h) - ellStar d| < ε := by
    have hc := (ell_p_continuousAt hd B).tendsto
    have hv : ell (B.p 0) = ellStar d := by rw [B.p_zero, ell_pStar hd]
    rw [hv] at hc
    have := Metric.tendsto_nhds.mp hc ε hε
    simpa [Real.dist_eq] using this
  have e3 : ∀ᶠ h in 𝓝 (0:ℝ), |B.gam h - gammaStar d| < ε := by
    have := Metric.tendsto_nhds.mp (tendsto_gam_nhds B) ε hε
    simpa [Real.dist_eq] using this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and (e2.and e3))
  refine ⟨min (min h0 B.h₀) δ, lt_min (lt_min hh0 B.h₀_pos) hδ,
    le_trans (min_le_left _ _) (min_le_right _ _), ε, hε, ?_⟩
  intro h hpos hlt u lv g hu hl hg hs ht L1 L2 L3
  have habs : |h| = h := abs_of_pos hpos
  have hh0' : |h| < h0 := by
    rw [habs]; exact lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhB : |h| < B.h₀ := by
    rw [habs]; exact lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhδ : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, habs]; exact lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨b1, b2, b3⟩ := hball hhδ
  have hne : h ≠ 0 := hpos.ne'
  have hc := huniq h hh0' hne u lv g hu hl hg hs (by linarith) (by nlinarith) (by nlinarith)
    (by nlinarith) L1 L2 L3
  -- the family point solves the same system
  have hp := B.p_mem h hhB
  have hs0 : 0 < B.u h - h := sVal_pos hhB
  have hs1 : B.u h - h < 1 := sVal_lt_one hhB
  have ht0 : 0 < B.u h + h := tVal_pos hhB
  have ht1 : B.u h + h < 1 := tVal_lt_one hhB
  have M1 : Lell d (ell (B.p h)) (B.gam h) ((B.u h - h) ^ 2) = 0 := by
    rw [Lell_eq_Fkkt hp.1 hp.2 (by positivity) (by nlinarith)]; exact B.kkt_ss h hhB
  have M2 : Lell d (ell (B.p h)) (B.gam h) ((B.u h - h) * (B.u h + h)) = 0 := by
    rw [Lell_eq_Fkkt hp.1 hp.2 (by positivity) (by nlinarith)]; exact B.kkt_st h hhB
  have M3 : Lell d (ell (B.p h)) (B.gam h) ((B.u h + h) ^ 2) = 0 := by
    rw [Lell_eq_Fkkt hp.1 hp.2 (by positivity) (by nlinarith)]; exact B.kkt_tt h hhB
  have hB := huniq h hh0' hne (B.u h) (ell (B.p h)) (B.gam h) b1 b2 b3 hs0 ht0
    (by nlinarith) (by nlinarith) (by nlinarith) M1 M2 M3
  rw [← hB] at hc
  simp only [Prod.mk.injEq] at hc
  exact hc

/-! ### Local exhaustiveness for a `d`-regular graph -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- `μ_* m (u_*^d)^{v-2} = γ_*`, with `μ_* = 1/(m r_*^m)`: the relation `γ = μ m q^{v-2}` at
the singular endpoint. -/
theorem muStar_mul_eq_gammaStar (hd : 2 ≤ d) (B : KKTFamily d) (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) :
    1 / ((H.edgeFinset.card : ℝ) * rStar d ^ H.edgeFinset.card) * (H.edgeFinset.card : ℝ)
      * (uStar d ^ d) ^ (Fintype.card V - 2) = gammaStar d := by
  have h := muVal_mul_eq_gam H hd hreg hcard (zero_mem_window B)
  rwa [B.muVal_zero hd, qVal_zero, B.gam_zero, Real.rpow_natCast] at h

/-- **Local exhaustiveness from the scalar conditions** (`lem:rank-one-kkt-family`, the
converse).  Given a window `h₀` on which the scalar converse `exists_scalar_converse` holds,
there is `ε > 0` such that every `(α, s, t, p, r, μ)` with `0 < α < 1`, `0 < s < t < 1`, the
parameters `s, t, p, r, μ` within `ε` of `u_*, u_*, p_*, r_*, 1/(m r_*^m)`, which solves the three
equations `F_{p,γ}(s²) = F_{p,γ}(st) = F_{p,γ}(t²) = 0` and the block balance with
`γ = μ m q^{v-2}`, `q = α s^d + (1-α) t^d`, and has `r^m = q^v`, is the family point at
`h = (t-s)/2 ∈ (0, h₀)`. -/
theorem exists_converse_of_scalar (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) {h₀ ε₁ : ℝ} (hh₀ : 0 < h₀) (hh₀B : h₀ ≤ B.h₀)
    (hε₁ : 0 < ε₁)
    (hconv : ∀ h : ℝ, 0 < h → h < h₀ → ∀ u lv g : ℝ,
        |u - uStar d| < ε₁ → |lv - ellStar d| < ε₁ → |g - gammaStar d| < ε₁ →
        0 < u - h → u + h < 1 →
        Lell d lv g ((u - h) ^ 2) = 0 → Lell d lv g ((u - h) * (u + h)) = 0 →
        Lell d lv g ((u + h) ^ 2) = 0 →
        u = B.u h ∧ lv = ell (B.p h) ∧ g = B.gam h) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ pStar d ∧ ε ≤ 1 - pStar d ∧
      ∀ α s t p r μ : ℝ, 0 < α → α < 1 → 0 < s → s < t → t < 1 →
        |s - uStar d| < ε → |t - uStar d| < ε → |p - pStar d| < ε → |r - rStar d| < ε →
        |μ - 1 / ((H.edgeFinset.card : ℝ) * rStar d ^ H.edgeFinset.card)| < ε →
        Fkkt d p (μ * (H.edgeFinset.card : ℝ)
          * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s ^ 2) = 0 →
        Fkkt d p (μ * (H.edgeFinset.card : ℝ)
          * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s * t) = 0 →
        Fkkt d p (μ * (H.edgeFinset.card : ℝ)
          * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (t ^ 2) = 0 →
        α * (Mfun d p (μ * (H.edgeFinset.card : ℝ)
              * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s ^ 2)
            - Mfun d p (μ * (H.edgeFinset.card : ℝ)
              * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s * t))
          = (1 - α) * (Mfun d p (μ * (H.edgeFinset.card : ℝ)
              * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (t ^ 2)
            - Mfun d p (μ * (H.edgeFinset.card : ℝ)
              * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (s * t)) →
        r ^ H.edgeFinset.card = (α * s ^ d + (1 - α) * t ^ d) ^ Fintype.card V →
        0 < (t - s) / 2 ∧ (t - s) / 2 < h₀ ∧
          s = B.sVal ((t - s) / 2) ∧ t = B.tVal ((t - s) / 2) ∧ p = B.p ((t - s) / 2) ∧
          r = B.rVal ((t - s) / 2) ∧
          μ = B.muVal (H.edgeFinset.card : ℝ) ((t - s) / 2) ∧ α = B.alph ((t - s) / 2) := by
  classical
  have hm : (0 : ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hcard
  -- continuity of `ℓ` at `p_*`
  obtain ⟨δℓ, hδℓ, hℓ⟩ := Metric.continuousAt_iff.mp (continuousAt_ell_pStar hd) ε₁ hε₁
  -- continuity of `(μ, q) ↦ μ m q^{v-2}` at `(μ_*, u_*^d)`
  have hG : Continuous (fun w : ℝ × ℝ =>
      w.1 * (H.edgeFinset.card : ℝ) * w.2 ^ (Fintype.card V - 2)) := by fun_prop
  obtain ⟨δ₁, hδ₁, hG1⟩ := Metric.continuousAt_iff.mp
    (hG.continuousAt (x := (1 / ((H.edgeFinset.card : ℝ) * rStar d ^ H.edgeFinset.card),
      uStar d ^ d))) ε₁ hε₁
  obtain ⟨δ₂, hδ₂, hP⟩ := Metric.continuousAt_iff.mp
    ((continuous_pow d).continuousAt (x := uStar d)) δ₁ hδ₁
  have hGv := muStar_mul_eq_gammaStar H hd B hreg hcard
  have hps0 := pStar_pos hd
  have hps1 := pStar_lt_one hd
  have hrs0 := rStar_pos hd
  set ε : ℝ := min h₀ (min ε₁ (min (pStar d) (min (1 - pStar d) (min δℓ (min (rStar d)
    (min δ₁ δ₂)))))) with hεdef
  have hεh : ε ≤ h₀ := min_le_left _ _
  have hεε : ε ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hεp0 : ε ≤ pStar d := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεp1 : ε ≤ 1 - pStar d := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hεℓ : ε ≤ δℓ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεr : ε ≤ rStar d := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))))
  have hε1 : ε ≤ δ₁ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))))
  have hε2 : ε ≤ δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))))
  have hεpos : 0 < ε := lt_min hh₀ (lt_min hε₁ (lt_min hps0 (lt_min (by linarith)
    (lt_min hδℓ (lt_min hrs0 (lt_min hδ₁ hδ₂))))))
  refine ⟨ε, hεpos, hεp0, hεp1, ?_⟩
  intro α s t p r μ hα0 hα1 hs0 hst ht1 hsu htu hpp hrr hμμ e1 e2 e3 hrow htd
  have hsu' := abs_lt.mp hsu
  have htu' := abs_lt.mp htu
  have hpp' := abs_lt.mp hpp
  have hrr' := abs_lt.mp hrr
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hr0 : 0 < r := by linarith
  -- the parameter distance of `ℓ(p)` and of `γ`
  have hl : |ell p - ellStar d| < ε₁ := by
    have := hℓ (show dist p (pStar d) < δℓ by rw [Real.dist_eq]; linarith)
    rwa [Real.dist_eq, ell_pStar hd] at this
  have hg : |μ * (H.edgeFinset.card : ℝ) * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)
      - gammaStar d| < ε₁ := by
    have hs' := hP (show dist s (uStar d) < δ₂ by rw [Real.dist_eq]; linarith)
    have ht' := hP (show dist t (uStar d) < δ₂ by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at hs' ht'
    have hQ : |α * s ^ d + (1 - α) * t ^ d - uStar d ^ d| < δ₁ := by
      have hsplit : α * s ^ d + (1 - α) * t ^ d - uStar d ^ d
          = α * (s ^ d - uStar d ^ d) + (1 - α) * (t ^ d - uStar d ^ d) := by ring
      have h1α : 0 < 1 - α := by linarith
      rw [hsplit]
      calc |α * (s ^ d - uStar d ^ d) + (1 - α) * (t ^ d - uStar d ^ d)|
          ≤ α * |s ^ d - uStar d ^ d| + (1 - α) * |t ^ d - uStar d ^ d| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_pos hα0, abs_of_pos h1α]
        _ < α * δ₁ + (1 - α) * δ₁ :=
            add_lt_add (mul_lt_mul_of_pos_left hs' hα0) (mul_lt_mul_of_pos_left ht' h1α)
        _ = δ₁ := by ring
    have hdist : dist ((μ, α * s ^ d + (1 - α) * t ^ d) : ℝ × ℝ)
        (1 / ((H.edgeFinset.card : ℝ) * rStar d ^ H.edgeFinset.card), uStar d ^ d) < δ₁ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt (by linarith) hQ
    have := hG1 hdist
    rw [Real.dist_eq] at this
    simp only at this
    rwa [hGv] at this
  -- move to the coordinates `u = (s+t)/2`, `h = (t-s)/2`
  generalize hgdef : μ * (H.edgeFinset.card : ℝ) * (α * s ^ d + (1 - α) * t ^ d)
    ^ (Fintype.card V - 2) = γ at hg e1 e2 e3 hrow
  have hus : (s + t) / 2 - (t - s) / 2 = s := by ring
  have hut : (s + t) / 2 + (t - s) / 2 = t := by ring
  have hpos : 0 < (t - s) / 2 := by linarith
  have hlt : (t - s) / 2 < h₀ := by linarith
  have hu : |(s + t) / 2 - uStar d| < ε₁ := by
    rw [abs_lt]; constructor <;> linarith
  have ht0 : 0 < t := hs0.trans hst
  have hs2 : s ^ 2 < s * t := by rw [sq]; exact mul_lt_mul_of_pos_left hst hs0
  have hst2 : s * t < t ^ 2 := by rw [sq]; exact mul_lt_mul_of_pos_right hst ht0
  have ht2 : t ^ 2 < 1 := pow_lt_one₀ ht0.le ht1 two_ne_zero
  have L1 : Lell d (ell p) γ (((s + t) / 2 - (t - s) / 2) ^ 2) = 0 := by
    rw [hus, Lell_eq_Fkkt hp0 hp1 (by positivity) (by linarith)]; exact e1
  have L2 : Lell d (ell p) γ (((s + t) / 2 - (t - s) / 2) * ((s + t) / 2 + (t - s) / 2)) = 0 := by
    rw [hus, hut, Lell_eq_Fkkt hp0 hp1 (by positivity) (by linarith)]; exact e2
  have L3 : Lell d (ell p) γ (((s + t) / 2 + (t - s) / 2) ^ 2) = 0 := by
    rw [hut, Lell_eq_Fkkt hp0 hp1 (by positivity) ht2]; exact e3
  obtain ⟨huB, hlB, hgB⟩ := hconv _ hpos hlt _ _ _ hu hl hg (by rw [hus]; exact hs0)
    (by rw [hut]; exact ht1) L1 L2 L3
  generalize hhdef : (t - s) / 2 = h at huB hlB hgB hpos hlt hus hut ⊢
  have hhB : |h| < B.h₀ := by rw [abs_of_pos hpos]; linarith
  have hsB : s = B.sVal h := by rw [sVal, ← huB, hus]
  have htB : t = B.tVal h := by rw [tVal, ← huB, hut]
  have hpB : p = B.p h := ell_injOn ⟨hp0, hp1⟩ (B.p_mem h hhB) hlB
  -- the block weight
  have hrowB := B.rowBalance h hhB
  rw [← hpB, ← hgB, ← huB, hus, hut] at hrowB
  have hαB : α = B.alph h :=
    rowBalance_weight_unique hd hp0 hp1 (by positivity) hs2 hst2 ht2 e1 e2 e3 hrow hrowB
  have hQB : α * s ^ d + (1 - α) * t ^ d = B.qVal h := by
    show α * s ^ d + (1 - α) * t ^ d = B.alph h * B.sVal h ^ d + (1 - B.alph h) * B.tVal h ^ d
    rw [← hαB, ← hsB, ← htB]
  -- the multiplier
  have hμB : μ = B.muVal (H.edgeFinset.card : ℝ) h := by
    have hmu := muVal_mul_eq_gam H hd hreg hcard hhB
    rw [← hgdef, hQB] at hgB
    have hq : 0 < (H.edgeFinset.card : ℝ) * B.qVal h ^ (Fintype.card V - 2) :=
      mul_pos hm (pow_pos (qVal_pos hhB) _)
    have hz : (μ - B.muVal (H.edgeFinset.card : ℝ) h)
        * ((H.edgeFinset.card : ℝ) * B.qVal h ^ (Fintype.card V - 2)) = 0 := by
      linear_combination hgB - hmu
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith
    · exact absurd hz hq.ne'
  -- the density
  have hrB : r = B.rVal h := by
    have hrv := rVal_pow_card_edges H hd hreg hhB
    rw [hQB, ← hrv] at htd
    exact (pow_left_inj₀ hr0.le (rVal_pos hd hhB).le (by omega)).mp htd
  exact ⟨hpos, hlt, hsB, htB, hpB, hrB, hμB, hαB⟩

/-- **Local exhaustiveness for the normalised two-block graphon** (`lem:rank-one-kkt-family`,
the converse in the precise sense stated after the lemma).  If `W_{α,s,t}` with `0 < α < 1`,
`0 < s < t < 1` satisfies the KKT conditions at `(p,r)` with multiplier `μ` and
`eq:block-stationarity`, and `(s, t, p, r, μ)` is within `ε` of
`(u_*, u_*, p_*, r_*, 1/(m r_*^m))`, then `h := (t-s)/2 ∈ (0, h₀)`,
`(s, t, p, r, μ, α) = (s_h, t_h, p_h, r_h, μ_h, α_h)`, and `W_{α,s,t} = W_h`.  (No closeness
of `α` to `1/2` is needed.) -/
theorem exists_converse_blockGraphon (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) {h₀ ε₁ : ℝ} (hh₀ : 0 < h₀) (hh₀B : h₀ ≤ B.h₀)
    (hε₁ : 0 < ε₁)
    (hconv : ∀ h : ℝ, 0 < h → h < h₀ → ∀ u lv g : ℝ,
        |u - uStar d| < ε₁ → |lv - ellStar d| < ε₁ → |g - gammaStar d| < ε₁ →
        0 < u - h → u + h < 1 →
        Lell d lv g ((u - h) ^ 2) = 0 → Lell d lv g ((u - h) * (u + h)) = 0 →
        Lell d lv g ((u + h) ^ 2) = 0 →
        u = B.u h ∧ lv = ell (B.p h) ∧ g = B.gam h) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (α s t p r μ : ℝ) (h11 : s ^ 2 ∈ Set.Icc (0:ℝ) 1) (h12 : s * t ∈ Set.Icc (0:ℝ) 1)
        (h22 : t ^ 2 ∈ Set.Icc (0:ℝ) 1),
        0 < α → α < 1 → 0 < s → s < t → t < 1 →
        SatisfiesKKT H p r μ (blockGraphon h11 h12 h22 α) →
        IsBlockStationary H p μ h11 h12 h22 α →
        |s - uStar d| < ε → |t - uStar d| < ε → |p - pStar d| < ε → |r - rStar d| < ε →
        |μ - 1 / ((H.edgeFinset.card : ℝ) * rStar d ^ H.edgeFinset.card)| < ε →
        ∃ hh : |(t - s) / 2| < B.h₀, 0 < (t - s) / 2 ∧ (t - s) / 2 < h₀ ∧
          s = B.sVal ((t - s) / 2) ∧ t = B.tVal ((t - s) / 2) ∧ p = B.p ((t - s) / 2) ∧
          r = B.rVal ((t - s) / 2) ∧
          μ = B.muVal (H.edgeFinset.card : ℝ) ((t - s) / 2) ∧ α = B.alph ((t - s) / 2) ∧
          ∀ x y : ℝ, (blockGraphon h11 h12 h22 α).toFun x y = (B.graphon hh).toFun x y := by
  classical
  obtain ⟨ε, hε, hεp0, hεp1, hcore⟩ :=
    exists_converse_of_scalar H hd hreg hcard hh₀ hh₀B hε₁ hconv
  refine ⟨ε, hε, ?_⟩
  intro α s t p r μ h11 h12 h22 hα0 hα1 hs0 hst ht1 hkkt hblock hsu htu hpp hrr hμμ
  have hpp' := abs_lt.mp hpp
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have ht0 : 0 < t := hs0.trans hst
  -- the everywhere-defined factor with pointwise bounds
  set g : ℝ → ℝ := fun x => if x ∈ Set.Icc (0:ℝ) α then s else t with hgdef
  have hη : 0 < min s (1 - t) := lt_min hs0 (by linarith)
  have hg0 : ∀ y, min s (1 - t) ≤ g y := by
    intro y
    by_cases hy : y ∈ Set.Icc (0:ℝ) α
    · simp only [hgdef, if_pos hy]; exact min_le_left _ _
    · simp only [hgdef, if_neg hy]; exact le_trans (min_le_left _ _) hst.le
  have hg1 : ∀ y, g y ≤ 1 - min s (1 - t) := by
    intro y
    have h2 : min s (1 - t) ≤ 1 - t := min_le_right _ _
    by_cases hy : y ∈ Set.Icc (0:ℝ) α
    · simp only [hgdef, if_pos hy]; linarith
    · simp only [hgdef, if_neg hy]; linarith
  have hgm : Measurable g := measurable_const.ite measurableSet_Icc measurable_const
  have hstat := isStationary_congr_ae (W' := rankOneGraphon hgm
      (fun y => le_trans hη.le (hg0 y)) (fun y => le_trans (hg1 y) (by linarith))) H
    (Eventually.of_forall fun z => bipodalValue_Icc_eq_ite α s t z.1 z.2) hkkt.2.2
  have hscal := kkt_scalar_of_stationary H hreg hp0 hp1 hη hgm hg0 hg1 hstat
  rw [integral_ite_pow hα0.le hα1.le d] at hscal
  obtain ⟨e1, e2, e3⟩ := three_values_of_ae (P := fun z => Fkkt d p (μ * (H.edgeFinset.card : ℝ)
      * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) z = 0) hα0 hα1
    (fun x hx => if_pos ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => if_neg fun h => absurd h.2 (not_le.mpr hx.1)) hscal
  rw [← sq] at e1 e3
  have hrow := rowBalance_of_blockStationary H hreg hcard hp0 hp1 h11 h12 h22 hα0 hα1 hblock
  have htd : r ^ H.edgeFinset.card = (α * s ^ d + (1 - α) * t ^ d) ^ Fintype.card V :=
    hkkt.2.1.symm.trans (tDensity_rankOne_two_block H hreg h11 h12 h22 hα0.le hα1.le)
  obtain ⟨hpos, hlt, hsB, htB, hpB, hrB, hμB, hαB⟩ :=
    hcore α s t p r μ hα0 hα1 hs0 hst ht1 hsu htu hpp hrr hμμ e1 e2 e3 hrow htd
  have hhB : |(t - s) / 2| < B.h₀ := by rw [abs_of_pos hpos]; linarith
  refine ⟨hhB, hpos, hlt, hsB, htB, hpB, hrB, hμB, hαB, fun x y => ?_⟩
  show bipodalValue (Set.Icc 0 α) (s ^ 2) (s * t) (t ^ 2) (x, y)
    = bipodalValue (Set.Icc 0 (B.alph ((t - s) / 2))) (B.sVal ((t - s) / 2) ^ 2)
      (B.sVal ((t - s) / 2) * B.tVal ((t - s) / 2)) (B.tVal ((t - s) / 2) ^ 2) (x, y)
  rw [← hsB, ← htB, ← hαB]

/-- **Local exhaustiveness for a nearby rank-one graphon** (`lem:rank-one-kkt-family`, the
converse assertion).  Let `W = f ⊗ f` with `f` measurable, `0 ≤ f ≤ 1`, `η ≤ f ≤ 1-η` a.e. and
`f` not a.e. constant, satisfying the KKT conditions at `(p,r)` with multiplier `μ`, with
`(p, r, μ)` within `ε` of `(p_*, r_*, 1/(m r_*^m))`.  Then `f` has a normal form
`f ∘ σ = f_{α,s,t}` (`lem:stationary-rank-one-bipodality`), and for every such normal form
satisfying `eq:block-stationarity` with `s, t` within `ε` of `u_*`: `h := (t-s)/2 ∈ (0,h₀)`,
`(s,t,p,r,μ,α) = (s_h,t_h,p_h,r_h,μ_h,α_h)`, `W_h(x,y) = W(σx,σy)` almost everywhere, and `h`
is the only positive index `h'` of the family for which `W_{h'}` is a relabelling of `W`. -/
theorem exists_converse_rankOne (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hcard : 1 ≤ H.edgeFinset.card) {h₀ ε₁ : ℝ} (hh₀ : 0 < h₀) (hh₀B : h₀ ≤ B.h₀)
    (hε₁ : 0 < ε₁)
    (hconv : ∀ h : ℝ, 0 < h → h < h₀ → ∀ u lv g : ℝ,
        |u - uStar d| < ε₁ → |lv - ellStar d| < ε₁ → |g - gammaStar d| < ε₁ →
        0 < u - h → u + h < 1 →
        Lell d lv g ((u - h) ^ 2) = 0 → Lell d lv g ((u - h) * (u + h)) = 0 →
        Lell d lv g ((u + h) ^ 2) = 0 →
        u = B.u h ∧ lv = ell (B.p h) ∧ g = B.gam h) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (f : ℝ → ℝ) (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
        (η p r μ : ℝ), 0 < η → (∀ᵐ y ∂unitμ, η ≤ f y ∧ f y ≤ 1 - η) →
        SatisfiesKKT H p r μ (rankOneGraphon hfm hf0 hf1) →
        (¬ ∃ c : ℝ, ∀ᵐ y ∂unitμ, f y = c) →
        |p - pStar d| < ε → |r - rStar d| < ε →
        |μ - 1 / ((H.edgeFinset.card : ℝ) * rStar d ^ H.edgeFinset.card)| < ε →
        (∃ α s t : ℝ, α ∈ Set.Ioo (0:ℝ) 1 ∧ 0 < s ∧ s < t ∧ t < 1 ∧
          ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
            ∀ᵐ x ∂unitμ, f (σ x)
              = (Set.Icc 0 α).indicator (fun _ => s) x + (Set.Ioc α 1).indicator (fun _ => t) x) ∧
        ∀ (α s t : ℝ) (σ : ℝ → ℝ) (h11 : s ^ 2 ∈ Set.Icc (0:ℝ) 1)
          (h12 : s * t ∈ Set.Icc (0:ℝ) 1) (h22 : t ^ 2 ∈ Set.Icc (0:ℝ) 1),
          0 < α → α < 1 → 0 < s → s < t → t < 1 → IsRelabelling σ →
          (∀ᵐ x ∂unitμ, f (σ x)
            = (Set.Icc 0 α).indicator (fun _ => s) x + (Set.Ioc α 1).indicator (fun _ => t) x) →
          IsBlockStationary H p μ h11 h12 h22 α →
          |s - uStar d| < ε → |t - uStar d| < ε →
          ∃ hh : |(t - s) / 2| < B.h₀, 0 < (t - s) / 2 ∧ (t - s) / 2 < h₀ ∧
            s = B.sVal ((t - s) / 2) ∧ t = B.tVal ((t - s) / 2) ∧ p = B.p ((t - s) / 2) ∧
            r = B.rVal ((t - s) / 2) ∧
            μ = B.muVal (H.edgeFinset.card : ℝ) ((t - s) / 2) ∧ α = B.alph ((t - s) / 2) ∧
            (∀ᵐ z ∂gμ, (B.graphon hh).toFun z.1 z.2
              = (rankOneGraphon hfm hf0 hf1).toFun (σ z.1) (σ z.2)) ∧
            ∀ (h' : ℝ) (hh' : |h'| < B.h₀), 0 < h' →
              (∃ τ : ℝ → ℝ, IsRelabelling τ ∧
                ∀ᵐ z ∂gμ, (B.graphon hh').toFun z.1 z.2
                  = (rankOneGraphon hfm hf0 hf1).toFun (τ z.1) (τ z.2)) →
              h' = (t - s) / 2 := by
  classical
  obtain ⟨ε, hε, hεp0, hεp1, hcore⟩ :=
    exists_converse_of_scalar H hd hreg hcard hh₀ hh₀B hε₁ hconv
  refine ⟨ε, hε, ?_⟩
  intro f hfm hf0 hf1 η p r μ hη hfη hkkt hnc hpp hrr hμμ
  have hpp' := abs_lt.mp hpp
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  refine ⟨stationary_rank_one_bipodality H hd hreg hp0 hp1 hfm hf0 hf1 hη hfη hkkt hnc, ?_⟩
  intro α s t σ h11 h12 h22 hα0 hα1 hs0 hst ht1 hσ hnf hblock hsu htu
  -- a pointwise-interior representative `g` of `f`
  obtain ⟨y₀, hy₀⟩ := hfη.exists
  have hη1 : η ≤ 1 - η := le_trans hy₀.1 hy₀.2
  set S : Set ℝ := {y | η ≤ f y ∧ f y ≤ 1 - η} with hSdef
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const hfm).inter (measurableSet_le hfm measurable_const)
  set g : ℝ → ℝ := S.piecewise f (fun _ => η) with hgdef
  have hgm : Measurable g := Measurable.piecewise hSm hfm measurable_const
  have hg0 : ∀ y, η ≤ g y := by
    intro y
    by_cases hy : y ∈ S
    · rw [hgdef, Set.piecewise_eq_of_mem _ _ _ hy]; exact hy.1
    · rw [hgdef, Set.piecewise_eq_of_notMem _ _ _ hy]
  have hg1 : ∀ y, g y ≤ 1 - η := by
    intro y
    by_cases hy : y ∈ S
    · rw [hgdef, Set.piecewise_eq_of_mem _ _ _ hy]; exact hy.2
    · rw [hgdef, Set.piecewise_eq_of_notMem _ _ _ hy]; exact hη1
  have hfg : ∀ᵐ y ∂unitμ, f y = g y := by
    filter_upwards [hfη] with y hy
    rw [hgdef, Set.piecewise_eq_of_mem _ _ _ (show y ∈ S from hy)]
  have hae2 : ∀ᵐ z ∂gμ, (rankOneGraphon hfm hf0 hf1).toFun z.1 z.2
      = (rankOneGraphon hgm (fun y => le_trans hη.le (hg0 y))
          (fun y => le_trans (hg1 y) (by linarith))).toFun z.1 z.2 := by
    filter_upwards [ae_gμ_of_ae_unitμ hfg] with z hz
    simp only [rankOneGraphon_toFun, hz.1, hz.2]
  have hscal := kkt_scalar_of_stationary H hreg hp0 hp1 hη hgm hg0 hg1
    (isStationary_congr_ae H hae2 hkkt.2.2)
  -- `∫ g^d = q = α s^d + (1-α) t^d`
  have hIcc : ∀ᵐ x ∂unitμ, x ∈ Set.Icc (0:ℝ) 1 := by
    rw [unitμ, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun x hx => hx
  have hnf' : ∀ᵐ x ∂unitμ, f (σ x) = if x ∈ Set.Icc (0:ℝ) α then s else t := by
    filter_upwards [hnf, hIcc] with x hx hx01
    rw [hx, indicator_factor_eq_ite hx01]
  have hint : ∫ y, g y ^ d ∂unitμ = α * s ^ d + (1 - α) * t ^ d := by
    have h1 : ∫ y, g y ^ d ∂unitμ = ∫ y, f y ^ d ∂unitμ :=
      integral_congr_ae (hfg.mono fun y hy => by simp only [hy])
    have h2 : ∫ x, f (σ x) ^ d ∂unitμ = ∫ y, f y ^ d ∂unitμ := by
      have h := integral_map (μ := unitμ) (φ := σ) hσ.measurable.aemeasurable
        (f := fun y => f y ^ d)
        (by rw [hσ.measurePreserving.map_eq]; exact (hfm.pow_const d).aestronglyMeasurable)
      rw [hσ.measurePreserving.map_eq] at h
      exact h.symm
    have h3 : ∫ x, f (σ x) ^ d ∂unitμ
        = ∫ x, (if x ∈ Set.Icc (0:ℝ) α then s else t) ^ d ∂unitμ :=
      integral_congr_ae (hnf'.mono fun x hx => by simp only [hx])
    rw [h1, ← h2, h3, integral_ite_pow hα0.le hα1.le d]
  rw [hint] at hscal
  -- pull the scalar equation back along `σ`
  have hpull := (hσ.measurePreserving.prod hσ.measurePreserving).quasiMeasurePreserving.ae
    (p := fun z : ℝ × ℝ => Fkkt d p (μ * (H.edgeFinset.card : ℝ)
      * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) (g z.1 * g z.2) = 0) hscal
  have hgσ : ∀ᵐ x ∂unitμ, g (σ x) = if x ∈ Set.Icc (0:ℝ) α then s else t := by
    filter_upwards [hσ.measurePreserving.quasiMeasurePreserving.ae hfg, hnf'] with x h1 h2
    rw [← h1, h2]
  have hfin : ∀ᵐ z ∂gμ, Fkkt d p (μ * (H.edgeFinset.card : ℝ)
      * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2))
      ((if z.1 ∈ Set.Icc (0:ℝ) α then s else t) * (if z.2 ∈ Set.Icc (0:ℝ) α then s else t))
        = 0 := by
    filter_upwards [hpull, ae_gμ_of_ae_unitμ hgσ] with z h1 h2
    rw [← h2.1, ← h2.2]
    exact h1
  obtain ⟨e1, e2, e3⟩ := three_values_of_ae (g := fun x => if x ∈ Set.Icc (0:ℝ) α then s else t)
    (P := fun z => Fkkt d p (μ * (H.edgeFinset.card : ℝ)
      * (α * s ^ d + (1 - α) * t ^ d) ^ (Fintype.card V - 2)) z = 0) hα0 hα1
    (fun x hx => if_pos ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => if_neg fun h => absurd h.2 (not_le.mpr hx.1)) hfin
  rw [← sq] at e1 e3
  have hrow := rowBalance_of_blockStationary H hreg hcard hp0 hp1 h11 h12 h22 hα0 hα1 hblock
  -- `W_{α,s,t}` is the relabelling of `W` along `σ`
  have hae3 : ∀ᵐ z ∂gμ, (blockGraphon h11 h12 h22 α).toFun z.1 z.2
      = (rankOneGraphon hfm hf0 hf1).toFun (σ z.1) (σ z.2) := by
    filter_upwards [ae_gμ_of_ae_unitμ hnf'] with z hz
    show bipodalValue (Set.Icc 0 α) (s ^ 2) (s * t) (t ^ 2) (z.1, z.2) = f (σ z.1) * f (σ z.2)
    rw [hz.1, hz.2, bipodalValue_Icc_eq_ite]
  have htd : r ^ H.edgeFinset.card = (α * s ^ d + (1 - α) * t ^ d) ^ Fintype.card V := by
    rw [← hkkt.2.1, ← tDensity_relabel hσ.measurePreserving H hae3]
    exact tDensity_rankOne_two_block H hreg h11 h12 h22 hα0.le hα1.le
  have hrr' := abs_lt.mp hrr
  obtain ⟨hpos, hlt, hsB, htB, hpB, hrB, hμB, hαB⟩ :=
    hcore α s t p r μ hα0 hα1 hs0 hst ht1 hsu htu hpp hrr hμμ e1 e2 e3 hrow htd
  have hhB : |(t - s) / 2| < B.h₀ := by rw [abs_of_pos hpos]; linarith
  have hWh : ∀ᵐ z ∂gμ, (B.graphon hhB).toFun z.1 z.2
      = (rankOneGraphon hfm hf0 hf1).toFun (σ z.1) (σ z.2) := by
    filter_upwards [hae3] with z hz
    rw [← hz]
    show bipodalValue (Set.Icc 0 (B.alph ((t - s) / 2))) (B.sVal ((t - s) / 2) ^ 2)
        (B.sVal ((t - s) / 2) * B.tVal ((t - s) / 2)) (B.tVal ((t - s) / 2) ^ 2) (z.1, z.2)
      = bipodalValue (Set.Icc 0 α) (s ^ 2) (s * t) (t ^ 2) (z.1, z.2)
    rw [← hsB, ← htB, ← hαB]
  refine ⟨hhB, hpos, hlt, hsB, htB, hpB, hrB, hμB, hαB, hWh, ?_⟩
  rintro h' hh' hpos' ⟨τ, hτ, hWτ⟩
  refine (eq_of_integral_comp_eq hhB hh' hpos hpos' fun φ hφ => ?_).symm
  have i1 : ∫ z, φ ((B.graphon hhB).toFun z.1 z.2) ∂gμ
      = ∫ z, φ ((rankOneGraphon hfm hf0 hf1).toFun (σ z.1) (σ z.2)) ∂gμ :=
    integral_congr_ae (hWh.mono fun z hz => by simp only [hz])
  have i2 : ∫ z, φ ((B.graphon hh').toFun z.1 z.2) ∂gμ
      = ∫ z, φ ((rankOneGraphon hfm hf0 hf1).toFun (τ z.1) (τ z.2)) ∂gμ :=
    integral_congr_ae (hWτ.mono fun z hz => by simp only [hz])
  rw [i1, i2, Graphon.integral_comp_relabel hσ.measurePreserving hφ,
    Graphon.integral_comp_relabel hτ.measurePreserving hφ]

end Graph

end KKTFamily

/-! ## `lem:rank-one-kkt-family` -/

/-- **`lem:rank-one-kkt-family` (analytic rank-one KKT family).**  For `d ≥ 2` and the family
`B` (`exists_kktFamily`), there is `h₀ > 0`, depending on `d` only (it is chosen before the
graph `H`), such that:

* `(u_0, p_0, γ_0, α_0) = (u_*, p_*, γ_*, 1/2)`, with `r_0 = r_*`;
* `u_h, p_h, γ_h, α_h` and `s_h, t_h, q_h, r_h` are real-analytic for `|h| < h₀`;
* `u_{-h} = u_h`, `p_{-h} = p_h`, `γ_{-h} = γ_h`, `α_{-h} = 1 - α_h`;
* `s_h = u_h - h`, `t_h = u_h + h`, `q_h = α_h s_h^d + (1-α_h) t_h^d`, `r_h = q_h^{2/d}`;
* `0 < p_h < r_h < 1`, `s_h, t_h, α_h ∈ (0,1)` for `|h| < h₀`;
* `eq:three-value-kkt` holds for `|h| < h₀`;
* `W_h = f_h ⊗ f_h` on `[0,1]²` with `f_h = f_{α_h,s_h,t_h}`, nonconstant for `h ≠ 0`;

and for every `d`-regular graph `H` with `m ≥ 1` edges and `v` vertices:

* `μ_h = γ_h/(m q_h^{v-2})` is real-analytic and positive for `|h| < h₀`, with
  `μ_0 = 1/(m r_*^m)`;
* for `|h| < h₀` (in particular for `0 < |h| < h₀`), `t(H, W_h) = r_h^m`, `W_h` satisfies the
  KKT conditions at `(p_h, r_h)` with multiplier `μ_h`, and `eq:block-stationarity` holds;
* **the converse**: there is `ε > 0` such that, if `W = f ⊗ f` is a nonconstant rank-one
  graphon with factor bounded away from `0` and `1` satisfying the KKT conditions at `(p, r)`
  with multiplier `μ`, and `(p, r, μ)` is within `ε` of `(p_*, r_*, 1/(m r_*^m))`, then `f` has a
  normal form `f ∘ σ = f_{α,s,t}` (`lem:stationary-rank-one-bipodality`), and for every normal
  form for which `eq:block-stationarity` holds and `s, t` are within `ε` of `u_*`,
  `h := (t-s)/2 ∈ (0, h₀)`, `(s,t,p,r,μ,α) = (s_h,t_h,p_h,r_h,μ_h,α_h)`, `W_h` is the
  relabelling of `W` along `σ`, and no other positive index `h'` has `W_{h'}` a relabelling
  of `W`.

The converse does not need `α` to be close to `1/2`. -/
theorem rank_one_kkt_family (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ B.h₀ ∧
      (B.u 0 = uStar d ∧ B.p 0 = pStar d ∧ B.gam 0 = gammaStar d ∧ B.alph 0 = 1 / 2 ∧
        B.rVal 0 = rStar d) ∧
      (∀ h : ℝ, |h| < h₀ →
        AnalyticAt ℝ B.u h ∧ AnalyticAt ℝ B.p h ∧ AnalyticAt ℝ B.gam h ∧
          AnalyticAt ℝ B.alph h ∧ AnalyticAt ℝ B.sVal h ∧ AnalyticAt ℝ B.tVal h ∧
          AnalyticAt ℝ B.qVal h ∧ AnalyticAt ℝ B.rVal h) ∧
      (∀ h : ℝ, |h| < h₀ →
        B.u (-h) = B.u h ∧ B.p (-h) = B.p h ∧ B.gam (-h) = B.gam h ∧
          B.alph (-h) = 1 - B.alph h) ∧
      (∀ h : ℝ, B.sVal h = B.u h - h ∧ B.tVal h = B.u h + h ∧
        B.qVal h = B.alph h * B.sVal h ^ d + (1 - B.alph h) * B.tVal h ^ d ∧
        B.rVal h = B.qVal h ^ (2 / (d : ℝ))) ∧
      (∀ h : ℝ, |h| < h₀ →
        0 < B.p h ∧ B.p h < B.rVal h ∧ B.rVal h < 1 ∧
          B.sVal h ∈ Set.Ioo (0:ℝ) 1 ∧ B.tVal h ∈ Set.Ioo (0:ℝ) 1 ∧
          B.alph h ∈ Set.Ioo (0:ℝ) 1) ∧
      (∀ h : ℝ, |h| < h₀ →
        ell (B.p h) - ell (B.sVal h ^ 2) = B.gam h * B.sVal h ^ (2 * d - 2) ∧
          ell (B.p h) - ell (B.sVal h * B.tVal h) = B.gam h * (B.sVal h * B.tVal h) ^ (d - 1) ∧
          ell (B.p h) - ell (B.tVal h ^ 2) = B.gam h * B.tVal h ^ (2 * d - 2)) ∧
      (∀ (h : ℝ) (hh : |h| < B.h₀), |h| < h₀ →
        (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
          (B.graphon hh).toFun x y
            = ((Set.Icc 0 (B.alph h)).indicator (fun _ => B.sVal h) x
                + (Set.Ioc (B.alph h) 1).indicator (fun _ => B.tVal h) x)
              * ((Set.Icc 0 (B.alph h)).indicator (fun _ => B.sVal h) y
                + (Set.Ioc (B.alph h) 1).indicator (fun _ => B.tVal h) y)) ∧
        (h ≠ 0 → ¬ ∃ ρ : ℝ, ∀ᵐ z ∂gμ, (B.graphon hh).toFun z.1 z.2 = ρ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∀ v, H.degree v = d) → 1 ≤ H.edgeFinset.card →
        (∀ h : ℝ, |h| < h₀ →
          B.muVal (H.edgeFinset.card : ℝ) h
              = B.gam h / ((H.edgeFinset.card : ℝ) * B.qVal h ^ (Fintype.card V - 2)) ∧
            AnalyticAt ℝ (B.muVal (H.edgeFinset.card : ℝ)) h ∧
            0 < B.muVal (H.edgeFinset.card : ℝ) h) ∧
        B.muVal (H.edgeFinset.card : ℝ) 0
          = 1 / ((H.edgeFinset.card : ℝ) * rStar d ^ H.edgeFinset.card) ∧
        (∀ (h : ℝ) (hh : |h| < B.h₀), |h| < h₀ →
          (B.graphon hh).tDensity H = B.rVal h ^ H.edgeFinset.card ∧
          SatisfiesKKT H (B.p h) (B.rVal h) (B.muVal (H.edgeFinset.card : ℝ) h) (B.graphon hh) ∧
          IsBlockStationary H (B.p h) (B.muVal (H.edgeFinset.card : ℝ) h)
            (KKTFamily.sq_sVal_mem hh) (KKTFamily.cross_mem hh) (KKTFamily.sq_tVal_mem hh)
            (B.alph h)) ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ (f : ℝ → ℝ) (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
            (η p r μ : ℝ), 0 < η → (∀ᵐ y ∂unitμ, η ≤ f y ∧ f y ≤ 1 - η) →
            SatisfiesKKT H p r μ (rankOneGraphon hfm hf0 hf1) →
            (¬ ∃ c : ℝ, ∀ᵐ y ∂unitμ, f y = c) →
            |p - pStar d| < ε → |r - rStar d| < ε →
            |μ - 1 / ((H.edgeFinset.card : ℝ) * rStar d ^ H.edgeFinset.card)| < ε →
            (∃ α s t : ℝ, α ∈ Set.Ioo (0:ℝ) 1 ∧ 0 < s ∧ s < t ∧ t < 1 ∧
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ x ∂unitμ, f (σ x)
                  = (Set.Icc 0 α).indicator (fun _ => s) x
                    + (Set.Ioc α 1).indicator (fun _ => t) x) ∧
            ∀ (α s t : ℝ) (σ : ℝ → ℝ) (h11 : s ^ 2 ∈ Set.Icc (0:ℝ) 1)
              (h12 : s * t ∈ Set.Icc (0:ℝ) 1) (h22 : t ^ 2 ∈ Set.Icc (0:ℝ) 1),
              0 < α → α < 1 → 0 < s → s < t → t < 1 → IsRelabelling σ →
              (∀ᵐ x ∂unitμ, f (σ x)
                = (Set.Icc 0 α).indicator (fun _ => s) x
                  + (Set.Ioc α 1).indicator (fun _ => t) x) →
              IsBlockStationary H p μ h11 h12 h22 α →
              |s - uStar d| < ε → |t - uStar d| < ε →
              ∃ hh : |(t - s) / 2| < B.h₀, 0 < (t - s) / 2 ∧ (t - s) / 2 < h₀ ∧
                s = B.sVal ((t - s) / 2) ∧ t = B.tVal ((t - s) / 2) ∧
                p = B.p ((t - s) / 2) ∧ r = B.rVal ((t - s) / 2) ∧
                μ = B.muVal (H.edgeFinset.card : ℝ) ((t - s) / 2) ∧
                α = B.alph ((t - s) / 2) ∧
                (∀ᵐ z ∂gμ, (B.graphon hh).toFun z.1 z.2
                  = (rankOneGraphon hfm hf0 hf1).toFun (σ z.1) (σ z.2)) ∧
                ∀ (h' : ℝ) (hh' : |h'| < B.h₀), 0 < h' →
                  (∃ τ : ℝ → ℝ, IsRelabelling τ ∧
                    ∀ᵐ z ∂gμ, (B.graphon hh').toFun z.1 z.2
                      = (rankOneGraphon hfm hf0 hf1).toFun (τ z.1) (τ z.2)) →
                  h' = (t - s) / 2 := by
  obtain ⟨h₁, hh₁, hh₁B, ε₁, hε₁, hconv⟩ := KKTFamily.exists_scalar_converse hd B
  obtain ⟨δ, hδ, hwin⟩ := KKTFamily.exists_window_p_lt_rVal hd B
  have hh₀ : 0 < min h₁ δ := lt_min hh₁ hδ
  have hh₀B : min h₁ δ ≤ B.h₀ := (min_le_left _ _).trans hh₁B
  have hmem : ∀ h : ℝ, |h| < min h₁ δ → |h| < B.h₀ := fun h hh => lt_of_lt_of_le hh hh₀B
  have hwin' : ∀ h : ℝ, |h| < min h₁ δ → B.p h < B.rVal h ∧ 0 < B.gam h :=
    fun h hh => hwin h (lt_of_lt_of_le hh (min_le_right _ _))
  refine ⟨min h₁ δ, hh₀, hh₀B, ⟨B.u_zero, B.p_zero, B.gam_zero, B.alph_zero,
    KKTFamily.rVal_zero hd B⟩, ?_, fun h _ => ⟨B.u_even h, B.p_even h, B.gam_even h,
    B.alph_reflect h⟩, fun h => ⟨rfl, rfl, rfl, rfl⟩, ?_,
    fun h hh => KKTFamily.three_value_kkt (hmem h hh), ?_, ?_⟩
  · intro h hh
    have hB := hmem h hh
    exact ⟨B.analyticAt_u h hB, B.analyticAt_p h hB, B.analyticAt_gam h hB,
      B.analyticAt_alph h hB, (B.analyticAt_u h hB).sub analyticAt_id,
      (B.analyticAt_u h hB).add analyticAt_id, KKTFamily.analyticAt_qVal hB,
      KKTFamily.analyticAt_rVal hB⟩
  · intro h hh
    have hB := hmem h hh
    exact ⟨(B.p_mem h hB).1, (hwin' h hh).1, KKTFamily.rVal_lt_one hd hB,
      ⟨KKTFamily.sVal_pos hB, KKTFamily.sVal_lt_one hB⟩,
      ⟨KKTFamily.tVal_pos hB, KKTFamily.tVal_lt_one hB⟩, B.alph_mem h hB⟩
  · intro h hh _
    exact ⟨fun x hx y hy => KKTFamily.graphon_toFun_eq_factor hh hx hy,
      fun hne => KKTFamily.graphon_not_ae_const hd hh hne⟩
  · intro V _ _ H _ hreg hcard
    have hm : (0 : ℝ) < (H.edgeFinset.card : ℝ) := by exact_mod_cast hcard
    refine ⟨fun h hh => ⟨KKTFamily.muVal_eq_div_pow H hd hreg hcard h,
      KKTFamily.analyticAt_muVal_of_mem hm (hmem h hh),
      KKTFamily.muVal_pos_of_gam_pos hm (hmem h hh) (hwin' h hh).2⟩, ?_,
      fun h hh hh' => ⟨KKTFamily.graphon_tDensity_eq_rVal_pow H hd hreg hh,
        KKTFamily.satisfiesKKT_graphon H hd hreg hcard hh (hwin' h hh').2.le,
        KKTFamily.isBlockStationary_graphon H hd hreg hcard hh⟩, ?_⟩
    · rw [B.muVal_zero hd, Real.rpow_natCast]
    · exact KKTFamily.exists_converse_rankOne H hd hreg hcard hh₀ hh₀B hε₁
        fun h hp hl => hconv h hp (lt_of_lt_of_le hl (min_le_left _ _))

end UpperTailOptimizers
