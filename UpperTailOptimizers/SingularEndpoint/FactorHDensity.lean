import UpperTailOptimizers.SingularEndpoint.Factor
import UpperTailOptimizers.SingularEndpoint.RankOne
import UpperTailOptimizers.SingularEndpoint.FactorStability

/-!
# The rank-one splitting of the `H`-density (Section 7, `paper/singular_endpoint.tex`)

This file formalises the third and largest of the three independent chunks of
`lem:localization-rank-one`, namely **`eq:rank-one-reduction-bounds`**,

`t(H, W) = q^v + R_H(f, E)`,  `|R_H(f, E)| ≤ C‖E‖₂³`.

The input is the structure `FactorDecomp d W` of `SingularEndpoint/Factor.lean`, which transcribes
the conclusion of the lemma as data: a nonnegative bounded factor `f` with the
orthogonality relation `∫ E(x,y) f(y)^{d-1} dy = 0` (the second half of
`eq:rank-one-orthogonality`), the rank-one part `A = f ⊗ f` and the residual
`E = W - A`.  Nothing here uses the `L^p` construction of `f`; the argument is exact
combinatorics plus two applications of Cauchy–Schwarz.

Because `Nonempty (FactorDecomp d W)` is vacuous (`f = 0` satisfies every field), the
estimate below is stated as an inequality between the *actual* quantities `t(H,W) - q^v`
and `‖E‖₂³` attached to the given decomposition; no closeness bound is assumed, and none
is needed — the bound holds for every `FactorDecomp`.

## The argument

Expand `t(H, W)` over `W = A + E` edge by edge (`Finset.prod_add` over `H.edgeFinset`):

`t(H, W) = ∑_{T ⊆ E(H)} ∫ (∏_{e ∈ T} E_e)(∏_{e ∈ E(H) \ T} A_e)`.

* `T = ∅` gives the rank-one term `∫ ∏_e A_e = (∫f^d)^{|V(H)|} = q^v`, because a rank-one
  kernel makes the edge product factor through the vertices
  (`prod_edges_eq_prod_pow_degree` of `SingularEndpoint/RankOne.lean`) and `H` is `d`-regular.
* **Any `T` with a vertex `w` of `T`-degree exactly one contributes zero.**  Splitting the
  edges of `H` at `w` into the single `T`-edge `s(w,u)` and the remaining `d - 1`
  `A`-edges, re-randomising the coordinate `x_w` produces the inner integral
  `∫ E(x_u, s) f(s)^{d-1} ds`, which is a.e. zero by the orthogonality field.
* The surviving `T` are nonempty and have **no vertex of `T`-degree one**, hence contain a
  three-edge walk `s(a,b), s(a,c), s(b,v)` (`exists_walk3`): the two extra edges at the two
  ends of any `T`-edge are distinct from it and from each other.  Integrating out the ends
  against Cauchy–Schwarz leaves `∫∫ |E(x,y)| g(x) g(y)` with `g(x) = (∫E(x,·)²)^{1/2}`, and
  one more Cauchy–Schwarz bounds that by `‖E‖₂³`.  This is where the exponent three comes
  from: three is the least number of edges a graph with no degree-one vertex can have.

The measure-theoretic engine is `integral_pi_update`: re-randomising one coordinate of a
product of probability measures leaves the integral unchanged, because
`(x, s) ↦ Function.update x w s` is measure preserving from `π ⊗ unitμ` to `π`.

## Contents

* `integral_mul_le_sqrt_mul_sqrt`, `integral_abs_le_sqrt` — Cauchy–Schwarz;
* `measurePreserving_update`, `integral_pi_update`, `integral_pi_le_of_update_le` — the
  one-coordinate resampling identity and the monotone form used throughout;
* `prod_edges_subset_eq_prod_pow_card` — the rank-one edge product for an arbitrary set of
  edges, refining `prod_edges_eq_prod_pow_degree`;
* `exists_walk3` — a nonempty edge set with no degree-one vertex contains a three-edge walk;
* `FactorDecomp.residL2`, `rowNorm` — `‖E‖₂` (as `√residSq`, `residSq` itself being
  `SingularEndpoint/FactorStability.lean`'s) and the row norms;
* `FactorDecomp.core_bound`, `FactorDecomp.walk3_bound` — `∫|E_{ab}E_{ac}E_{bv}| ≤ ‖E‖₂³`;
* `FactorDecomp.tDensity_expand` — the exact edge expansion (step (a));
* `FactorDecomp.integral_edgeA_prod` — the rank-one term `q^v`;
* `FactorDecomp.integral_term_eq_zero` — the vanishing of the degree-one terms (step (b));
* `FactorDecomp.abs_integral_term_le` — the `‖E‖₂³` bound on a surviving term (step (c));
* `FactorDecomp.abs_tDensity_sub_qVal_pow_le` and `FactorDecomp.tDensity_eq_qVal_pow_add` —
  **`eq:rank-one-reduction-bounds`** with `C = 40^{|E(H)|}` (step (d)).
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory

/-! ## Cauchy–Schwarz -/

/-- The scalar step of Cauchy–Schwarz: from `√A·√B·C ≤ A·B`, together with `C ≤ 0` in the
degenerate case `A·B = 0`, one gets `C ≤ √A·√B`. -/
private theorem cs_aux {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : Real.sqrt A * Real.sqrt B * C ≤ A * B) (hz : A * B = 0 → C ≤ 0) :
    C ≤ Real.sqrt A * Real.sqrt B := by
  have hsq : Real.sqrt A * Real.sqrt B * (Real.sqrt A * Real.sqrt B) = A * B := by
    rw [← pow_two, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  rcases eq_or_lt_of_le (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)) with hk | hk
  · exact le_trans (hz (by rw [← hsq, ← hk]; ring)) (le_of_eq hk)
  · exact le_of_mul_le_mul_left (by rw [hsq]; exact h) hk

/-- **Cauchy–Schwarz for the Bochner integral**: `∫ f·g ≤ (∫f²)^{1/2}(∫g²)^{1/2}`.

Expanding `0 ≤ ∫ (√(∫g²)·f - √(∫f²)·g)²` gives `√(∫f²)·√(∫g²)·∫fg ≤ (∫f²)(∫g²)`; the
degenerate case `(∫f²)(∫g²) = 0` forces `f = 0` or `g = 0` almost everywhere. -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) (hfg : Integrable (fun x => f x * g x) μ) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hA : (0:ℝ) ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hB : (0:ℝ) ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  refine cs_aux hA hB ?_ ?_
  · have h0 : (0:ℝ) ≤ ∫ x, (Real.sqrt (∫ t, g t ^ 2 ∂μ) * f x
        - Real.sqrt (∫ t, f t ^ 2 ∂μ) * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have e1 : Real.sqrt (∫ t, f t ^ 2 ∂μ) ^ 2 = ∫ t, f t ^ 2 ∂μ := Real.sq_sqrt hA
    have e2 : Real.sqrt (∫ t, g t ^ 2 ∂μ) ^ 2 = ∫ t, g t ^ 2 ∂μ := Real.sq_sqrt hB
    have hpt : ∀ x, (Real.sqrt (∫ t, g t ^ 2 ∂μ) * f x - Real.sqrt (∫ t, f t ^ 2 ∂μ) * g x) ^ 2
        = (∫ t, g t ^ 2 ∂μ) * f x ^ 2
          - 2 * (Real.sqrt (∫ t, f t ^ 2 ∂μ) * Real.sqrt (∫ t, g t ^ 2 ∂μ)) * (f x * g x)
          + (∫ t, f t ^ 2 ∂μ) * g x ^ 2 := by
      intro x
      linear_combination (f x ^ 2) * e2 + (g x ^ 2) * e1
    have hi1 : Integrable (fun x => (∫ t, g t ^ 2 ∂μ) * f x ^ 2) μ := hf2.const_mul _
    have hi2 : Integrable (fun x => 2 * (Real.sqrt (∫ t, f t ^ 2 ∂μ)
        * Real.sqrt (∫ t, g t ^ 2 ∂μ)) * (f x * g x)) μ := hfg.const_mul _
    have hi3 : Integrable (fun x => (∫ t, f t ^ 2 ∂μ) * g x ^ 2) μ := hg2.const_mul _
    have hi12 : Integrable (fun x => (∫ t, g t ^ 2 ∂μ) * f x ^ 2
        - 2 * (Real.sqrt (∫ t, f t ^ 2 ∂μ) * Real.sqrt (∫ t, g t ^ 2 ∂μ))
          * (f x * g x)) μ := hi1.sub hi2
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add hi12 hi3, integral_sub hi1 hi2, integral_const_mul,
      integral_const_mul, integral_const_mul] at h0
    nlinarith [h0]
  · intro hAB
    have key : ∀ {p q : α → ℝ}, Integrable (fun x => p x ^ 2) μ → (∫ x, p x ^ 2 ∂μ) = 0 →
        (fun x => p x * q x) =ᵐ[μ] 0 := by
      intro p q hp2 hp
      have hp0 : (fun x => p x ^ 2) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hp2).mp hp
      filter_upwards [hp0] with x hx
      have hx' : p x ^ 2 = 0 := by simpa using hx
      have hx0 : p x = 0 := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hx'
      simp [hx0]
    rcases mul_eq_zero.mp hAB with h | h
    · rw [integral_congr_ae (key hf2 h)]; simp
    · have h' : (fun x => g x * f x) =ᵐ[μ] 0 := key hg2 h
      have h'' : (fun x => f x * g x) =ᵐ[μ] 0 := by
        filter_upwards [h'] with x hx
        simpa [mul_comm] using hx
      rw [integral_congr_ae h'']; simp

/-- Cauchy–Schwarz against the constant `1` on a probability space: `∫ |f| ≤ (∫f²)^{1/2}`. -/
theorem integral_abs_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, |f x| ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have habs2 : Integrable (fun x => |f x| ^ 2) μ := by simpa [sq_abs] using hf2
  have hone : Integrable (fun _ : α => (1:ℝ) ^ 2) μ := by simp
  have hprod : Integrable (fun x => |f x| * (1:ℝ)) μ := by simpa using hf.abs
  have h := integral_mul_le_sqrt_mul_sqrt (μ := μ) (f := fun x => |f x|)
    (g := fun _ => (1:ℝ)) habs2 hone hprod
  have h1 : ∫ x, |f x| * (1:ℝ) ∂μ = ∫ x, |f x| ∂μ := by simp
  have h2 : ∫ x, |f x| ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ := by simp [sq_abs]
  have h3 : ∫ _x : α, (1:ℝ) ^ 2 ∂μ = 1 := by simp
  rw [h1, h2, h3, Real.sqrt_one, mul_one] at h
  exact h

/-! ## Re-randomising one coordinate of a product measure -/

/-- `(x, s) ↦ Function.update x w s` is measurable. -/
private theorem measurable_updateAt {ι : Type*} [DecidableEq ι] (w : ι) :
    Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 w p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i = w
  · subst h
    have he : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2 i) = fun p => p.2 := by
      funext p; simp
    rw [he]; exact measurable_snd
  · have he : (fun p : (ι → ℝ) × ℝ => Function.update p.1 w p.2 i) = fun p => p.1 i := by
      funext p; simp [Function.update_of_ne h]
    rw [he]; exact (measurable_pi_apply i).comp measurable_fst

/-- **Re-randomising one coordinate preserves the product measure**: the map
`(x, s) ↦ Function.update x w s` pushes `π ⊗ unitμ` forward to `π`, where `π` is the
product of copies of `unitμ` indexed by `ι`.

The pre-image of a box `∏ᵢ sᵢ` is `(∏_{i ≠ w} sᵢ) × s_w`, whose product measure is
`∏ᵢ unitμ(sᵢ)`; `Measure.pi_eq` then identifies the push-forward with `π`. -/
theorem measurePreserving_update {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 w p.2)
      ((Measure.pi fun _ : ι => unitμ).prod unitμ) (Measure.pi fun _ : ι => unitμ) := by
  classical
  refine ⟨measurable_updateAt w, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 w p.2) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi (Function.update s w Set.univ)) ×ˢ s w := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro hp
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = w
        · subst hi; rw [Function.update_self]; exact Set.mem_univ _
        · rw [Function.update_of_ne hi]
          have hpi := hp i
          rwa [Function.update_of_ne hi] at hpi
      · have hpw := hp w
        rwa [Function.update_self] at hpw
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = w
      · subst hi; rwa [Function.update_self]
      · rw [Function.update_of_ne hi]
        have h1i := h1 i
        rwa [Function.update_of_ne hi] at h1i
  have hrest : (∏ i ∈ Finset.univ.erase w, unitμ (Function.update s w Set.univ i))
      = ∏ i ∈ Finset.univ.erase w, unitμ (s i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [Measure.map_apply (measurable_updateAt w) (MeasurableSet.univ_pi hs), hpre,
    Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ (fun i => unitμ (s i)) (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ
      (fun i => unitμ (Function.update s w Set.univ i)) (Finset.mem_univ w),
    Function.update_self, measure_univ, hrest]
  ring

/-- **The one-coordinate resampling identity**: for a bounded measurable `F`,
`∫ F(x) dπ = ∫ (∫ F(update x w s) ds) dπ`.  Immediate from `measurePreserving_update`
and Fubini. -/
theorem integral_pi_update {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι)
    {F : (ι → ℝ) → ℝ} (hF : Measurable F) {C : ℝ} (hb : ∀ x, |F x| ≤ C) :
    ∫ x, F x ∂(Measure.pi fun _ : ι => unitμ)
      = ∫ x, (∫ s, F (Function.update x w s) ∂unitμ) ∂(Measure.pi fun _ : ι => unitμ) := by
  have hmp := measurePreserving_update (ι := ι) w
  have hint : Integrable (fun p : (ι → ℝ) × ℝ => F (Function.update p.1 w p.2))
      ((Measure.pi fun _ : ι => unitμ).prod unitμ) :=
    integrable_of_abs_le (hF.comp (measurable_updateAt w)) C fun p => hb _
  have step1 : ∫ x, F x ∂(Measure.pi fun _ : ι => unitμ)
      = ∫ p, F (Function.update p.1 w p.2)
          ∂((Measure.pi fun _ : ι => unitμ).prod unitμ) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map (measurable_updateAt w).aemeasurable hF.aestronglyMeasurable
  rw [step1, integral_prod _ hint]

/-- The partially integrated function `x ↦ ∫ F(update x w s) ds` is measurable. -/
theorem measurable_integral_update {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι)
    {F : (ι → ℝ) → ℝ} (hF : Measurable F) :
    Measurable (fun x : ι → ℝ => ∫ s, F (Function.update x w s) ∂unitμ) := by
  have h : StronglyMeasurable (fun p : (ι → ℝ) × ℝ => F (Function.update p.1 w p.2)) :=
    (hF.comp (measurable_updateAt w)).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- **The monotone form of the resampling identity.**  If, for every `x`, the inner
integral over the `w`-coordinate is at most `Φ x`, then `∫ F ≤ ∫ Φ`. -/
theorem integral_pi_le_of_update_le {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι)
    {F Φ : (ι → ℝ) → ℝ} {C D : ℝ} (hF : Measurable F) (hΦ : Measurable Φ)
    (hbF : ∀ y, |F y| ≤ C) (hbΦ : ∀ y, |Φ y| ≤ D)
    (hle : ∀ y, ∫ s, F (Function.update y w s) ∂unitμ ≤ Φ y) :
    ∫ y, F y ∂(Measure.pi fun _ : ι => unitμ)
      ≤ ∫ y, Φ y ∂(Measure.pi fun _ : ι => unitμ) := by
  rw [integral_pi_update w hF hbF]
  refine integral_mono ?_ (integrable_of_abs_le hΦ D hbΦ) hle
  refine integrable_of_abs_le (measurable_integral_update w hF) C fun y => ?_
  have hnorm : ‖∫ s, F (Function.update y w s) ∂unitμ‖ ≤ C * unitμ.real Set.univ :=
    norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hbF _)
  have huniv : C * unitμ.real Set.univ = C := by simp [measureReal_def]
  rw [huniv] at hnorm
  simpa [Real.norm_eq_abs] using hnorm

/-! ## The rank-one edge product over an arbitrary set of edges -/

/-- **The rank-one edge product factors through the vertices, for an arbitrary edge set.**
For any finset `S` of non-diagonal elements of `Sym2 V` and any weight `g`,
`∏_{e = pq ∈ S} g p · g q = ∏_v g v ^ #{e ∈ S : v ∈ e}`.

This is `prod_edges_eq_prod_pow_degree` of `SingularEndpoint/RankOne.lean` with `H.edgeFinset`
replaced by an arbitrary sub-collection; the counting argument is the same, with the
incidence finset replaced by `S.filter (v ∈ ·)`. -/
theorem prod_edges_subset_eq_prod_pow_card {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Sym2 V)) (hS : ∀ e ∈ S, ¬ e.IsDiag) (g : V → ℝ) :
    ∏ e ∈ S, Sym2.lift ⟨fun p q => g p * g q, fun _ _ => mul_comm _ _⟩ e
      = ∏ v, g v ^ (S.filter fun e => v ∈ e).card := by
  classical
  have hpow : ∀ v : V, g v ^ (S.filter fun e => v ∈ e).card
      = ∏ _e ∈ S.filter fun e => v ∈ e, g v := fun v => (Finset.prod_const _).symm
  have hcomm : (∏ v, ∏ _e ∈ S.filter fun e => v ∈ e, g v)
      = ∏ e ∈ S, ∏ v ∈ Finset.univ.filter fun v => v ∈ e, g v := by
    refine Finset.prod_comm' ?_
    intro v e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [Finset.prod_congr rfl fun v _ => hpow v, hcomm]
  refine (Finset.prod_congr rfl fun e he => ?_).symm
  induction e using Sym2.ind with
  | _ p q =>
    have hpq : p ≠ q := fun h => hS _ he (Sym2.mk_isDiag_iff.mpr h)
    have hset : (Finset.univ.filter fun v => v ∈ s(p, q)) = {p, q} := by
      ext v; simp [Sym2.mem_iff]
    rw [hset, Finset.prod_insert (by simpa using hpq), Finset.prod_singleton]
    rfl

/-! ## A nonempty edge set with no degree-one vertex contains a three-edge walk -/

/-- **Three edges out of a degree-one-free edge set.**  If `T` is a nonempty set of edges of
`H` in which no vertex has degree exactly one, then `T` contains three distinct edges
`s(a,b)`, `s(a,c)`, `s(b,v)` forming a walk (possibly a triangle, when `c = v`).

Take any `e₀ = s(a,b) ∈ T`.  Both `a` and `b` have `T`-degree at least one, hence at least
two, so there are further `T`-edges `s(a,c) ≠ e₀` and `s(b,v) ≠ e₀`; and `s(a,c) ≠ s(b,v)`
because `b` lies on the second and not on the first.  In particular a surviving `T` has at
least three edges — the source of the exponent three in
`eq:rank-one-reduction-bounds`. -/
theorem exists_walk3 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {T : Finset (Sym2 V)} (hT : T ⊆ H.edgeFinset) (hTne : T.Nonempty)
    (hdeg : ∀ w : V, (T.filter fun e => w ∈ e).card ≠ 1) :
    ∃ a b c v : V, s(a, b) ∈ T ∧ s(a, c) ∈ T ∧ s(b, v) ∈ T ∧
      s(a, b) ≠ s(a, c) ∧ s(a, b) ≠ s(b, v) ∧ s(a, c) ≠ s(b, v) ∧
      a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ v ≠ a ∧ v ≠ b := by
  classical
  have hnd : ∀ e ∈ T, ¬ e.IsDiag := fun e he =>
    H.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hT he))
  obtain ⟨e₀, he₀⟩ := hTne
  revert he₀
  induction e₀ using Sym2.ind with
  | _ a b =>
    intro he₀
    have hab : a ≠ b := fun h => hnd _ he₀ (Sym2.mk_isDiag_iff.mpr h)
    -- a second `T`-edge at `a`
    have hmema : s(a, b) ∈ T.filter fun e => a ∈ e := by
      simp only [Finset.mem_filter]
      exact ⟨he₀, Sym2.mem_mk_left a b⟩
    have hcarda : 2 ≤ (T.filter fun e => a ∈ e).card := by
      have h1 : 0 < (T.filter fun e => a ∈ e).card := Finset.card_pos.mpr ⟨_, hmema⟩
      have h2 := hdeg a
      omega
    have hnea : ((T.filter fun e => a ∈ e).erase s(a, b)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hmema]
      omega
    obtain ⟨e₁, he₁⟩ := hnea
    have h1ne : e₁ ≠ s(a, b) := Finset.ne_of_mem_erase he₁
    have h1mem : e₁ ∈ T ∧ a ∈ e₁ := by
      have := Finset.mem_of_mem_erase he₁
      simpa only [Finset.mem_filter] using this
    -- a second `T`-edge at `b`
    have hmemb : s(a, b) ∈ T.filter fun e => b ∈ e := by
      simp only [Finset.mem_filter]
      exact ⟨he₀, Sym2.mem_mk_right a b⟩
    have hcardb : 2 ≤ (T.filter fun e => b ∈ e).card := by
      have h1 : 0 < (T.filter fun e => b ∈ e).card := Finset.card_pos.mpr ⟨_, hmemb⟩
      have h2 := hdeg b
      omega
    have hneb : ((T.filter fun e => b ∈ e).erase s(a, b)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hmemb]
      omega
    obtain ⟨e₂, he₂⟩ := hneb
    have h2ne : e₂ ≠ s(a, b) := Finset.ne_of_mem_erase he₂
    have h2mem : e₂ ∈ T ∧ b ∈ e₂ := by
      have := Finset.mem_of_mem_erase he₂
      simpa only [Finset.mem_filter] using this
    -- name the far endpoints
    refine ⟨a, b, Sym2.Mem.other h1mem.2, Sym2.Mem.other h2mem.2, he₀, ?_, ?_, ?_, ?_, ?_,
      hab, ?_, ?_, ?_, ?_⟩
    · rw [Sym2.other_spec h1mem.2]; exact h1mem.1
    · have hs : s(b, Sym2.Mem.other h2mem.2) = e₂ := Sym2.other_spec h2mem.2
      rw [hs]; exact h2mem.1
    · intro h
      exact h1ne (by rw [← Sym2.other_spec h1mem.2, ← h])
    · intro h
      exact h2ne (by rw [← Sym2.other_spec h2mem.2, ← h])
    · -- `b` lies on the third edge but not on the second
      intro h
      have hb2 : b ∈ s(a, Sym2.Mem.other h1mem.2) := by
        rw [h]; exact Sym2.mem_mk_left b _
      rcases Sym2.mem_iff.mp hb2 with h' | h'
      · exact hab h'.symm
      · exact h1ne (by rw [← Sym2.other_spec h1mem.2, h'])
    · exact Sym2.other_ne (hnd _ h1mem.1) h1mem.2
    · intro h
      exact h1ne (by rw [← Sym2.other_spec h1mem.2, h])
    · intro h
      exact h2ne (by rw [← Sym2.other_spec h2mem.2, h, Sym2.eq_swap])
    · exact Sym2.other_ne (hnd _ h2mem.1) h2mem.2

variable {d : ℕ} {W : Graphon}

namespace FactorDecomp

variable (P : FactorDecomp d W)

/-! ## The residual `L²` norms -/

/-- The residual `E = W - f ⊗ f` is symmetric, because `W` is. -/
theorem resid_symm (x y : ℝ) : P.resid x y = P.resid y x := by
  show W.toFun x y - P.f x * P.f y = W.toFun y x - P.f y * P.f x
  rw [W.symm' x y]; ring

/-- The residual norm `‖E‖₂`.  The squared norm `residSq`, its nonnegativity and the
integrability of `E²` come from `SingularEndpoint/FactorStability.lean`, which owns that family. -/
noncomputable def residL2 : ℝ := Real.sqrt P.residSq

/-- `residL2` is `SingularEndpoint/FactorStability.lean`'s `residNorm` under another name; the two files
were written independently and this records that they agree. -/
theorem residL2_eq_residNorm : P.residL2 = P.residNorm := rfl

/-- `‖E‖₂ ≥ 0`. -/
theorem residL2_nonneg : 0 ≤ P.residL2 := Real.sqrt_nonneg _

/-- `‖E‖₂² is the square of ‖E‖₂`. -/
theorem residL2_sq : P.residL2 ^ 2 = P.residSq := Real.sq_sqrt P.residSq_nonneg

/-- The row norm `g(t) = (∫ E(t,s)² ds)^{1/2}` of the residual. -/
noncomputable def rowNorm (t : ℝ) : ℝ := Real.sqrt (∫ s, P.resid t s ^ 2 ∂unitμ)

/-- The row norm is nonnegative. -/
theorem rowNorm_nonneg (t : ℝ) : 0 ≤ P.rowNorm t := Real.sqrt_nonneg _

/-- The row norm is bounded by `5`, since `|E| ≤ 5`. -/
theorem rowNorm_le (t : ℝ) : P.rowNorm t ≤ 5 := by
  have hle : (∫ s, P.resid t s ^ 2 ∂unitμ) ≤ 25 := by
    have hint : Integrable (fun s => P.resid t s ^ 2) unitμ :=
      integrable_of_abs_le ((P.measurable_resid_right t).pow_const 2) 25 fun s => by
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_abs (P.resid t s), P.abs_resid_le t s, abs_nonneg (P.resid t s)]
    have := integral_mono hint (integrable_const (25:ℝ)) fun s => by
      nlinarith [sq_abs (P.resid t s), P.abs_resid_le t s, abs_nonneg (P.resid t s)]
    simpa using this
  calc P.rowNorm t ≤ Real.sqrt 25 := Real.sqrt_le_sqrt hle
    _ = 5 := by
        rw [show (25:ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]

/-- The row norm is measurable. -/
theorem measurable_rowNorm : Measurable P.rowNorm := by
  have h : Measurable fun t : ℝ => ∫ s, P.resid t s ^ 2 ∂unitμ :=
    ((P.measurable_resid.pow_const 2).stronglyMeasurable).integral_prod_right'.measurable
  exact Real.continuous_sqrt.measurable.comp h

/-- Fubini: `∫ g(t)² dt = ‖E‖₂²`. -/
theorem integral_rowNorm_sq : ∫ t, P.rowNorm t ^ 2 ∂unitμ = P.residSq := by
  have hpt : ∀ t : ℝ, P.rowNorm t ^ 2 = ∫ s, P.resid t s ^ 2 ∂unitμ := fun t =>
    Real.sq_sqrt (integral_nonneg fun s => sq_nonneg _)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  show ∫ t, ∫ s, P.resid t s ^ 2 ∂unitμ ∂unitμ = ∫ z, P.resid z.1 z.2 ^ 2 ∂gμ
  exact integral_integral P.integrable_resid_sq

/-- `∫ |E(t,s)| ds ≤ g(t)`, by Cauchy–Schwarz on the probability space. -/
theorem integral_abs_resid_le (t : ℝ) : ∫ s, |P.resid t s| ∂unitμ ≤ P.rowNorm t := by
  have h1 : Integrable (fun s => P.resid t s) unitμ :=
    integrable_of_abs_le (P.measurable_resid_right t) 5 fun s => P.abs_resid_le t s
  have h2 : Integrable (fun s => P.resid t s ^ 2) unitμ :=
    integrable_of_abs_le ((P.measurable_resid_right t).pow_const 2) 25 fun s => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (P.resid t s), P.abs_resid_le t s, abs_nonneg (P.resid t s)]
  exact integral_abs_le_sqrt h1 h2

/-- `∫ |E(t,s)| |E(t',s)| ds ≤ g(t) g(t')`, by Cauchy–Schwarz. -/
theorem integral_abs_resid_mul_le (t t' : ℝ) :
    ∫ s, |P.resid t s| * |P.resid t' s| ∂unitμ ≤ P.rowNorm t * P.rowNorm t' := by
  have hsq : ∀ r : ℝ, Integrable (fun s => |P.resid r s| ^ 2) unitμ := fun r =>
    integrable_of_abs_le (((P.measurable_resid_right r).abs).pow_const 2) 25 fun s => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (P.resid r s), P.abs_resid_le r s, abs_nonneg (P.resid r s)]
  have hmul : Integrable (fun s => |P.resid t s| * |P.resid t' s|) unitμ :=
    integrable_of_abs_le (((P.measurable_resid_right t).abs).mul
      ((P.measurable_resid_right t').abs)) 25 fun s => by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [P.abs_resid_le t s, P.abs_resid_le t' s, abs_nonneg (P.resid t s),
        abs_nonneg (P.resid t' s)]
  have h := integral_mul_le_sqrt_mul_sqrt (μ := unitμ) (f := fun s => |P.resid t s|)
    (g := fun s => |P.resid t' s|) (hsq t) (hsq t') hmul
  have e1 : ∫ s, |P.resid t s| ^ 2 ∂unitμ = ∫ s, P.resid t s ^ 2 ∂unitμ := by simp [sq_abs]
  have e2 : ∫ s, |P.resid t' s| ^ 2 ∂unitμ = ∫ s, P.resid t' s ^ 2 ∂unitμ := by simp [sq_abs]
  rw [e1, e2] at h
  exact h

/-! ## The three-edge bound -/

/-- `y ↦ E(y a, y b)` is measurable on the vertex product space. -/
theorem measurable_residAt {V : Type*} (a b : V) :
    Measurable fun y : V → ℝ => P.resid (y a) (y b) := by
  have hpair : Measurable fun y : V → ℝ => (y a, y b) := by fun_prop
  exact P.measurable_resid.comp hpair

/-- `y ↦ g(y a)` is measurable on the vertex product space. -/
theorem measurable_rowNormAt {V : Type*} (a : V) :
    Measurable fun y : V → ℝ => P.rowNorm (y a) :=
  P.measurable_rowNorm.comp (measurable_pi_apply a)

/-- **The core Cauchy–Schwarz bound**: for distinct vertices `a ≠ b`,
`∫ |E(y a, y b)| g(y a) g(y b) ≤ ‖E‖₂³`.

The pair marginal of the product measure at two distinct coordinates is `gμ`, and then
Cauchy–Schwarz against `‖E‖₂` leaves `(∫g²)^{1/2·2} = ‖E‖₂²`. -/
theorem core_bound {V : Type*} [Fintype V] [DecidableEq V] {a b : V} (hab : a ≠ b) :
    ∫ y : V → ℝ, |P.resid (y a) (y b)| * P.rowNorm (y a) * P.rowNorm (y b)
        ∂(Measure.pi fun _ : V => unitμ) ≤ P.residL2 ^ 3 := by
  have hmeasZ : Measurable fun z : ℝ × ℝ =>
      |P.resid z.1 z.2| * P.rowNorm z.1 * P.rowNorm z.2 :=
    ((P.measurable_resid.abs).mul (P.measurable_rowNorm.comp measurable_fst)).mul
      (P.measurable_rowNorm.comp measurable_snd)
  have htrans : ∫ y : V → ℝ, |P.resid (y a) (y b)| * P.rowNorm (y a) * P.rowNorm (y b)
        ∂(Measure.pi fun _ : V => unitμ)
      = ∫ z : ℝ × ℝ, |P.resid z.1 z.2| * P.rowNorm z.1 * P.rowNorm z.2 ∂gμ := by
    have hmp := measurePreserving_pair (V := V) hab
    show _ = ∫ z : ℝ × ℝ, |P.resid z.1 z.2| * P.rowNorm z.1 * P.rowNorm z.2
      ∂(unitμ.prod unitμ)
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hmeasZ.aestronglyMeasurable]
  rw [htrans]
  -- Cauchy–Schwarz with `f = |E|` and `g = g ⊗ g`
  have hf2 : Integrable (fun z : ℝ × ℝ => |P.resid z.1 z.2| ^ 2) gμ :=
    integrable_of_abs_le ((P.measurable_resid.abs).pow_const 2) 25 fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [P.abs_resid_le z.1 z.2, abs_nonneg (P.resid z.1 z.2)]
  have hrow : ∀ z : ℝ × ℝ, P.rowNorm z.1 * P.rowNorm z.2 ≤ 25 := fun z => by
    nlinarith [P.rowNorm_le z.1, P.rowNorm_le z.2, P.rowNorm_nonneg z.1,
      P.rowNorm_nonneg z.2]
  have hrow0 : ∀ z : ℝ × ℝ, (0:ℝ) ≤ P.rowNorm z.1 * P.rowNorm z.2 := fun z =>
    mul_nonneg (P.rowNorm_nonneg z.1) (P.rowNorm_nonneg z.2)
  have hg2 : Integrable (fun z : ℝ × ℝ => (P.rowNorm z.1 * P.rowNorm z.2) ^ 2) gμ :=
    integrable_of_abs_le (((P.measurable_rowNorm.comp measurable_fst).mul
      (P.measurable_rowNorm.comp measurable_snd)).pow_const 2) 625 fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hrow z, hrow0 z]
  have hfg : Integrable
      (fun z : ℝ × ℝ => |P.resid z.1 z.2| * (P.rowNorm z.1 * P.rowNorm z.2)) gμ :=
    integrable_of_abs_le ((P.measurable_resid.abs).mul
      ((P.measurable_rowNorm.comp measurable_fst).mul
        (P.measurable_rowNorm.comp measurable_snd))) 125 fun z => by
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (hrow0 z))]
      nlinarith [P.abs_resid_le z.1 z.2, abs_nonneg (P.resid z.1 z.2), hrow z, hrow0 z]
  have hcs := integral_mul_le_sqrt_mul_sqrt (μ := gμ) hf2 hg2 hfg
  have hre : ∫ z : ℝ × ℝ, |P.resid z.1 z.2| * P.rowNorm z.1 * P.rowNorm z.2 ∂gμ
      = ∫ z : ℝ × ℝ, |P.resid z.1 z.2| * (P.rowNorm z.1 * P.rowNorm z.2) ∂gμ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have e1 : ∫ z : ℝ × ℝ, |P.resid z.1 z.2| ^ 2 ∂gμ = P.residSq := by
    simp only [residSq, sq_abs]
  have e2 : ∫ z : ℝ × ℝ, (P.rowNorm z.1 * P.rowNorm z.2) ^ 2 ∂gμ = P.residSq ^ 2 := by
    have hpt : ∀ z : ℝ × ℝ, (P.rowNorm z.1 * P.rowNorm z.2) ^ 2
        = P.rowNorm z.1 ^ 2 * P.rowNorm z.2 ^ 2 := fun z => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      show gμ = unitμ.prod unitμ from rfl,
      integral_prod_mul (fun t : ℝ => P.rowNorm t ^ 2) (fun t : ℝ => P.rowNorm t ^ 2),
      P.integral_rowNorm_sq]
    ring
  rw [hre]
  refine le_trans hcs (le_of_eq ?_)
  rw [e1, e2, Real.sqrt_sq P.residSq_nonneg]
  show P.residL2 * P.residSq = P.residL2 ^ 3
  rw [← P.residL2_sq]; ring

/-- **Integrating out a leaf coordinate.**  If `K` does not depend on the coordinate `w`,
then `∫ K·|E(y a, y w)| ≤ ∫ K·g(y a)`. -/
theorem peel_leaf {V : Type*} [Fintype V] [DecidableEq V] {w a : V} (haw : a ≠ w)
    {K : (V → ℝ) → ℝ} {CK : ℝ} (hK : Measurable K) (hKb : ∀ y, |K y| ≤ CK)
    (hKnn : ∀ y, 0 ≤ K y) (hKupd : ∀ y s, K (Function.update y w s) = K y) :
    ∫ y : V → ℝ, K y * |P.resid (y a) (y w)| ∂(Measure.pi fun _ : V => unitμ)
      ≤ ∫ y : V → ℝ, K y * P.rowNorm (y a) ∂(Measure.pi fun _ : V => unitμ) := by
  refine integral_pi_le_of_update_le w (C := CK * 5) (D := CK * 5)
    (hK.mul ((P.measurable_residAt a w).abs))
    (hK.mul (P.measurable_rowNormAt a)) (fun y => ?_) (fun y => ?_) (fun y => ?_)
  · rw [abs_mul, abs_abs]
    exact mul_le_mul (hKb y) (P.abs_resid_le _ _) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hKb y))
  · rw [abs_mul, abs_of_nonneg (P.rowNorm_nonneg _)]
    exact mul_le_mul (hKb y) (P.rowNorm_le _) (P.rowNorm_nonneg _)
      (le_trans (abs_nonneg _) (hKb y))
  · have hupd : ∀ s : ℝ, K (Function.update y w s)
        * |P.resid (Function.update y w s a) (Function.update y w s w)|
        = K y * |P.resid (y a) s| := by
      intro s
      rw [hKupd, Function.update_of_ne haw, Function.update_self]
    calc ∫ s, K (Function.update y w s)
          * |P.resid (Function.update y w s a) (Function.update y w s w)| ∂unitμ
        = ∫ s, K y * |P.resid (y a) s| ∂unitμ :=
          integral_congr_ae (Filter.Eventually.of_forall hupd)
      _ = K y * ∫ s, |P.resid (y a) s| ∂unitμ := integral_const_mul _ _
      _ ≤ K y * P.rowNorm (y a) :=
          mul_le_mul_of_nonneg_left (P.integral_abs_resid_le (y a)) (hKnn y)

/-- **Integrating out a coordinate shared by two residual edges.**  If `K` does not depend
on `w`, then `∫ K·|E(y a, y w)|·|E(y b, y w)| ≤ ∫ K·g(y a)·g(y b)`. -/
theorem peel_double {V : Type*} [Fintype V] [DecidableEq V] {w a b : V} (haw : a ≠ w)
    (hbw : b ≠ w) {K : (V → ℝ) → ℝ} {CK : ℝ} (hK : Measurable K) (hKb : ∀ y, |K y| ≤ CK)
    (hKnn : ∀ y, 0 ≤ K y) (hKupd : ∀ y s, K (Function.update y w s) = K y) :
    ∫ y : V → ℝ, K y * (|P.resid (y a) (y w)| * |P.resid (y b) (y w)|)
        ∂(Measure.pi fun _ : V => unitμ)
      ≤ ∫ y : V → ℝ, K y * (P.rowNorm (y a) * P.rowNorm (y b))
        ∂(Measure.pi fun _ : V => unitμ) := by
  refine integral_pi_le_of_update_le w (C := CK * 25) (D := CK * 25)
    (hK.mul (((P.measurable_residAt a w).abs).mul ((P.measurable_residAt b w).abs)))
    (hK.mul ((P.measurable_rowNormAt a).mul (P.measurable_rowNormAt b)))
    (fun y => ?_) (fun y => ?_) (fun y => ?_)
  · have h2 : (0:ℝ) ≤ |P.resid (y a) (y w)| * |P.resid (y b) (y w)| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h1 : |P.resid (y a) (y w)| * |P.resid (y b) (y w)| ≤ 25 := by
      nlinarith [P.abs_resid_le (y a) (y w), P.abs_resid_le (y b) (y w),
        abs_nonneg (P.resid (y a) (y w)), abs_nonneg (P.resid (y b) (y w))]
    calc |K y * (|P.resid (y a) (y w)| * |P.resid (y b) (y w)|)|
        = |K y| * (|P.resid (y a) (y w)| * |P.resid (y b) (y w)|) := by
          rw [abs_mul, abs_of_nonneg h2]
      _ ≤ CK * 25 := mul_le_mul (hKb y) h1 h2 (le_trans (abs_nonneg _) (hKb y))
  · have h2 : (0:ℝ) ≤ P.rowNorm (y a) * P.rowNorm (y b) :=
      mul_nonneg (P.rowNorm_nonneg _) (P.rowNorm_nonneg _)
    have h1 : P.rowNorm (y a) * P.rowNorm (y b) ≤ 25 := by
      nlinarith [P.rowNorm_le (y a), P.rowNorm_le (y b), P.rowNorm_nonneg (y a),
        P.rowNorm_nonneg (y b)]
    calc |K y * (P.rowNorm (y a) * P.rowNorm (y b))|
        = |K y| * (P.rowNorm (y a) * P.rowNorm (y b)) := by
          rw [abs_mul, abs_of_nonneg h2]
      _ ≤ CK * 25 := mul_le_mul (hKb y) h1 h2 (le_trans (abs_nonneg _) (hKb y))
  · have hupd : ∀ s : ℝ, K (Function.update y w s)
        * (|P.resid (Function.update y w s a) (Function.update y w s w)|
          * |P.resid (Function.update y w s b) (Function.update y w s w)|)
        = K y * (|P.resid (y a) s| * |P.resid (y b) s|) := by
      intro s
      rw [hKupd, Function.update_of_ne haw, Function.update_of_ne hbw, Function.update_self]
    calc ∫ s, K (Function.update y w s)
          * (|P.resid (Function.update y w s a) (Function.update y w s w)|
            * |P.resid (Function.update y w s b) (Function.update y w s w)|) ∂unitμ
        = ∫ s, K y * (|P.resid (y a) s| * |P.resid (y b) s|) ∂unitμ :=
          integral_congr_ae (Filter.Eventually.of_forall hupd)
      _ = K y * ∫ s, |P.resid (y a) s| * |P.resid (y b) s| ∂unitμ := integral_const_mul _ _
      _ ≤ K y * (P.rowNorm (y a) * P.rowNorm (y b)) :=
          mul_le_mul_of_nonneg_left (P.integral_abs_resid_mul_le (y a) (y b)) (hKnn y)

/-- **The three-edge walk bound.**  For a walk `s(a,b), s(a,c), s(b,v)` (with `c = v`
allowed, i.e. a triangle),

`∫ |E(y a, y b)| |E(y a, y c)| |E(y b, y v)| ≤ ‖E‖₂³`.

In the triangle case the shared coordinate `c = v` is integrated out by `peel_double`; in
the path case the two ends `c` and `v` are integrated out one at a time by `peel_leaf`.
Either way one lands on `core_bound`. -/
theorem walk3_bound {V : Type*} [Fintype V] [DecidableEq V] {a b c v : V} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hva : v ≠ a) (hvb : v ≠ b) :
    ∫ y : V → ℝ, |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)|
        ∂(Measure.pi fun _ : V => unitμ) ≤ P.residL2 ^ 3 := by
  by_cases hcv : c = v
  · subst hcv
    -- the triangle case: peel the shared coordinate `c`
    have hK : Measurable fun y : V → ℝ => |P.resid (y a) (y b)| :=
      (P.measurable_residAt a b).abs
    have hKb : ∀ y : V → ℝ, |(|P.resid (y a) (y b)|)| ≤ 5 := fun y => by
      rw [abs_abs]; exact P.abs_resid_le _ _
    have hKnn : ∀ y : V → ℝ, 0 ≤ |P.resid (y a) (y b)| := fun y => abs_nonneg _
    have hKupd : ∀ (y : V → ℝ) (s : ℝ),
        |P.resid (Function.update y c s a) (Function.update y c s b)|
          = |P.resid (y a) (y b)| := fun y s => by
      rw [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hcb)]
    have hstep := P.peel_double (w := c) (a := a) (b := b) (Ne.symm hca) (Ne.symm hcb)
      hK hKb hKnn hKupd
    have hre1 : ∫ y : V → ℝ,
          |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y c)|
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ,
          |P.resid (y a) (y b)| * (|P.resid (y a) (y c)| * |P.resid (y b) (y c)|)
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have hre2 : ∫ y : V → ℝ,
          |P.resid (y a) (y b)| * (P.rowNorm (y a) * P.rowNorm (y b))
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ, |P.resid (y a) (y b)| * P.rowNorm (y a) * P.rowNorm (y b)
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [hre1]
    exact le_trans (le_trans hstep (le_of_eq hre2)) (P.core_bound hab)
  · -- the path case: peel `c`, then `v`
    have hvc : v ≠ c := fun h => hcv h.symm
    have hK1 : Measurable fun y : V → ℝ =>
        |P.resid (y a) (y b)| * |P.resid (y b) (y v)| :=
      ((P.measurable_residAt a b).abs).mul ((P.measurable_residAt b v).abs)
    have hK1b : ∀ y : V → ℝ,
        |(|P.resid (y a) (y b)| * |P.resid (y b) (y v)|)| ≤ 25 := fun y => by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [P.abs_resid_le (y a) (y b), P.abs_resid_le (y b) (y v),
        abs_nonneg (P.resid (y a) (y b)), abs_nonneg (P.resid (y b) (y v))]
    have hK1nn : ∀ y : V → ℝ, 0 ≤ |P.resid (y a) (y b)| * |P.resid (y b) (y v)| :=
      fun y => by positivity
    have hK1upd : ∀ (y : V → ℝ) (s : ℝ),
        |P.resid (Function.update y c s a) (Function.update y c s b)|
          * |P.resid (Function.update y c s b) (Function.update y c s v)|
        = |P.resid (y a) (y b)| * |P.resid (y b) (y v)| := fun y s => by
      rw [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hcb),
        Function.update_of_ne hvc]
    have hstep1 := P.peel_leaf (w := c) (a := a) (Ne.symm hca) hK1 hK1b hK1nn hK1upd
    have hK2 : Measurable fun y : V → ℝ => |P.resid (y a) (y b)| * P.rowNorm (y a) :=
      ((P.measurable_residAt a b).abs).mul (P.measurable_rowNormAt a)
    have hK2nn : ∀ y : V → ℝ, 0 ≤ |P.resid (y a) (y b)| * P.rowNorm (y a) := fun y =>
      mul_nonneg (abs_nonneg _) (P.rowNorm_nonneg _)
    have hK2b : ∀ y : V → ℝ, |(|P.resid (y a) (y b)| * P.rowNorm (y a))| ≤ 25 := fun y => by
      rw [abs_of_nonneg (hK2nn y)]
      nlinarith [P.abs_resid_le (y a) (y b), abs_nonneg (P.resid (y a) (y b)),
        P.rowNorm_le (y a), P.rowNorm_nonneg (y a)]
    have hK2upd : ∀ (y : V → ℝ) (s : ℝ),
        |P.resid (Function.update y v s a) (Function.update y v s b)|
          * P.rowNorm (Function.update y v s a)
        = |P.resid (y a) (y b)| * P.rowNorm (y a) := fun y s => by
      rw [Function.update_of_ne (Ne.symm hva), Function.update_of_ne (Ne.symm hvb)]
    have hstep2 := P.peel_leaf (w := v) (a := b) (Ne.symm hvb) hK2 hK2b hK2nn hK2upd
    have hre1 : ∫ y : V → ℝ,
          |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)|
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ,
          (|P.resid (y a) (y b)| * |P.resid (y b) (y v)|) * |P.resid (y a) (y c)|
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have hre2 : ∫ y : V → ℝ,
          (|P.resid (y a) (y b)| * |P.resid (y b) (y v)|) * P.rowNorm (y a)
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ,
          (|P.resid (y a) (y b)| * P.rowNorm (y a)) * |P.resid (y b) (y v)|
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have hre3 : ∫ y : V → ℝ,
          (|P.resid (y a) (y b)| * P.rowNorm (y a)) * P.rowNorm (y b)
          ∂(Measure.pi fun _ : V => unitμ)
        = ∫ y : V → ℝ, |P.resid (y a) (y b)| * P.rowNorm (y a) * P.rowNorm (y b)
          ∂(Measure.pi fun _ : V => unitμ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [hre1]
    refine le_trans hstep1 (le_trans (le_of_eq hre2) (le_trans hstep2 ?_))
    exact le_trans (le_of_eq hre3) (P.core_bound hab)

/-! ## The edge factors and the binomial expansion -/

/-- The rank-one factor `A(y p, y q) = f(y p) f(y q)` attached to an edge. -/
def edgeA {V : Type*} (y : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun p q => P.f (y p) * P.f (y q), fun _ _ => mul_comm _ _⟩ e

/-- The residual factor `E(y p, y q)` attached to an edge. -/
def edgeE {V : Type*} (y : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun p q => P.resid (y p) (y q), fun _ _ => P.resid_symm _ _⟩ e

/-- The rank-one factor is bounded by `4`. -/
theorem abs_edgeA_le {V : Type*} (y : V → ℝ) (e : Sym2 V) : |P.edgeA y e| ≤ 4 := by
  induction e using Sym2.ind with
  | _ p q => exact P.abs_rankOne_le (y p) (y q)

/-- The residual factor is bounded by `5`. -/
theorem abs_edgeE_le {V : Type*} (y : V → ℝ) (e : Sym2 V) : |P.edgeE y e| ≤ 5 := by
  induction e using Sym2.ind with
  | _ p q => exact P.abs_resid_le (y p) (y q)

/-- The rank-one factor is measurable in the vertex assignment. -/
theorem measurable_edgeA {V : Type*} (e : Sym2 V) :
    Measurable fun y : V → ℝ => P.edgeA y e := by
  induction e using Sym2.ind with
  | _ p q =>
    exact (P.meas_f.comp (measurable_pi_apply p)).mul (P.meas_f.comp (measurable_pi_apply q))

/-- The residual factor is measurable in the vertex assignment. -/
theorem measurable_edgeE {V : Type*} (e : Sym2 V) :
    Measurable fun y : V → ℝ => P.edgeE y e := by
  induction e using Sym2.ind with
  | _ p q => exact P.measurable_residAt p q

/-- The generic term of the edge expansion is measurable. -/
theorem measurable_termFun {V : Type*} [Fintype V] [DecidableEq V]
    (T S : Finset (Sym2 V)) :
    Measurable fun y : V → ℝ => (∏ e ∈ T, P.edgeE y e) * ∏ e ∈ S, P.edgeA y e :=
  (Finset.measurable_prod _ fun e _ => P.measurable_edgeE e).mul
    (Finset.measurable_prod _ fun e _ => P.measurable_edgeA e)

/-- The generic term of the edge expansion is uniformly bounded by `5^m·4^m`. -/
theorem abs_termFun_le {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {T : Finset (Sym2 V)} (hT : T ⊆ H.edgeFinset) (y : V → ℝ) :
    |(∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e|
      ≤ 5 ^ H.edgeFinset.card * 4 ^ H.edgeFinset.card := by
  rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
  have h1 : ∏ e ∈ T, |P.edgeE y e| ≤ 5 ^ H.edgeFinset.card := by
    calc ∏ e ∈ T, |P.edgeE y e| ≤ ∏ _e ∈ T, (5:ℝ) :=
          Finset.prod_le_prod (fun e _ => abs_nonneg _) fun e _ => P.abs_edgeE_le y e
      _ = 5 ^ T.card := Finset.prod_const _
      _ ≤ 5 ^ H.edgeFinset.card :=
          pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hT)
  have h2 : ∏ e ∈ H.edgeFinset \ T, |P.edgeA y e| ≤ 4 ^ H.edgeFinset.card := by
    calc ∏ e ∈ H.edgeFinset \ T, |P.edgeA y e| ≤ ∏ _e ∈ H.edgeFinset \ T, (4:ℝ) :=
          Finset.prod_le_prod (fun e _ => abs_nonneg _) fun e _ => P.abs_edgeA_le y e
      _ = 4 ^ (H.edgeFinset \ T).card := Finset.prod_const _
      _ ≤ 4 ^ H.edgeFinset.card :=
          pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Finset.sdiff_subset))
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun e _ => abs_nonneg _) (by positivity)

/-- **The exact edge expansion (step (a))**: expanding `W = A + E` over the edges of `H`,

`t(H, W) = ∑_{T ⊆ E(H)} ∫ (∏_{e ∈ T} E_e)(∏_{e ∈ E(H) \ T} A_e)`.

This is `Finset.prod_add` inside the integral, with `integral_finset_sum` to exchange the
finite sum and the integral. -/
theorem tDensity_expand {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] :
    W.tDensity H = ∑ T ∈ H.edgeFinset.powerset,
      ∫ y : V → ℝ, (∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e
        ∂(Measure.pi fun _ : V => unitμ) := by
  classical
  have hpt : ∀ y : V → ℝ,
      (∏ e ∈ H.edgeFinset, Sym2.lift ⟨fun p q => W.toFun (y p) (y q),
          fun p q => W.symm' (y p) (y q)⟩ e)
      = ∑ T ∈ H.edgeFinset.powerset,
          (∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e := by
    intro y
    rw [← Finset.prod_add]
    refine Finset.prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ p q =>
      show W.toFun (y p) (y q) = P.resid (y p) (y q) + P.f (y p) * P.f (y q)
      show W.toFun (y p) (y q) = W.toFun (y p) (y q) - P.f (y p) * P.f (y q)
        + P.f (y p) * P.f (y q)
      ring
  have hint : ∀ T ∈ H.edgeFinset.powerset,
      Integrable (fun y : V → ℝ => (∏ e ∈ T, P.edgeE y e)
        * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e) (Measure.pi fun _ : V => unitμ) := by
    intro T hTmem
    exact integrable_of_abs_le (P.measurable_termFun T (H.edgeFinset \ T))
      (5 ^ H.edgeFinset.card * 4 ^ H.edgeFinset.card)
      fun y => P.abs_termFun_le H (Finset.mem_powerset.mp hTmem) y
  show ∫ y : V → ℝ, _ ∂(Measure.pi fun _ : V => unitμ) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum _ hint]

/-- **The rank-one term**: for `d`-regular `H`, `∫ ∏_{e} A_e = q^{|V(H)|}`.

The rank-one edge product factors through the vertices with exponent `deg v = d`, and the
product measure integrates a product of one-coordinate functions coordinatewise. -/
theorem integral_edgeA_prod {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) :
    ∫ y : V → ℝ, (∏ e ∈ H.edgeFinset, P.edgeA y e) ∂(Measure.pi fun _ : V => unitμ)
      = P.qVal ^ Fintype.card V := by
  have hpt : ∀ y : V → ℝ, (∏ e ∈ H.edgeFinset, P.edgeA y e) = ∏ v, P.f (y v) ^ d := by
    intro y
    calc ∏ e ∈ H.edgeFinset, P.edgeA y e = ∏ v, P.f (y v) ^ H.degree v :=
          prod_edges_eq_prod_pow_degree H fun v => P.f (y v)
      _ = ∏ v, P.f (y v) ^ d := Finset.prod_congr rfl fun v _ => by rw [hreg v]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_fintype_prod_eq_pow (ι := V) (fun t : ℝ => P.f t ^ d)]
  rfl

/-! ## The vanishing of the degree-one terms -/

/-- **Step (b): a term with a vertex of residual degree one vanishes.**

If some vertex `w` lies on exactly one edge `s(w,u)` of `T`, then the `d - 1` remaining
edges of `H` at `w` are all `A`-edges, so re-randomising the coordinate `x_w` turns the
term into `(stuff independent of x_w) · ∫ E(x_u, s) f(s)^{d-1} ds`, and the inner integral
is a.e. zero by the orthogonality field `FactorDecomp.ortho`
`eq:rank-one-orthogonality`. -/
theorem integral_term_eq_zero {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) {T : Finset (Sym2 V)}
    (hT : T ⊆ H.edgeFinset) {w : V} (hw : (T.filter fun e => w ∈ e).card = 1) :
    ∫ y : V → ℝ, (∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e
      ∂(Measure.pi fun _ : V => unitμ) = 0 := by
  classical
  -- the unique `T`-edge at `w`
  obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp hw
  have he₀mem : e₀ ∈ T ∧ w ∈ e₀ := by
    have hmem : e₀ ∈ T.filter fun e => w ∈ e := by
      rw [he₀]; exact Finset.mem_singleton_self e₀
    simpa only [Finset.mem_filter] using hmem
  have huniq : ∀ e ∈ T, w ∈ e → e = e₀ := by
    intro e heT hwe
    have hmem : e ∈ T.filter fun e => w ∈ e := Finset.mem_filter.mpr ⟨heT, hwe⟩
    rw [he₀, Finset.mem_singleton] at hmem
    exact hmem
  have hnd : ¬ e₀.IsDiag :=
    H.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hT he₀mem.1))
  have hspec : s(w, Sym2.Mem.other he₀mem.2) = e₀ := Sym2.other_spec he₀mem.2
  have huw : Sym2.Mem.other he₀mem.2 ≠ w := Sym2.other_ne hnd he₀mem.2
  -- the `A`-degree of `w` is `d - 1`
  have hSdeg : ((H.edgeFinset \ T).filter fun e => w ∈ e).card = d - 1 := by
    have hsub : (T.filter fun e => w ∈ e) ⊆ H.edgeFinset.filter fun e => w ∈ e :=
      Finset.filter_subset_filter _ hT
    have hsplit : ((H.edgeFinset \ T).filter fun e => w ∈ e)
        = (H.edgeFinset.filter fun e => w ∈ e) \ (T.filter fun e => w ∈ e) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    have hdegw : (H.edgeFinset.filter fun e => w ∈ e).card = d := by
      rw [show (H.edgeFinset.filter fun e => w ∈ e) = H.incidenceFinset w from
        (H.incidenceFinset_eq_filter w).symm, SimpleGraph.card_incidenceFinset_eq_degree,
        hreg]
    rw [hsplit, Finset.card_sdiff_of_subset hsub, hdegw, hw]
  -- the `A`-part factors through the vertices
  have hSnd : ∀ e ∈ H.edgeFinset \ T, ¬ e.IsDiag := fun e he =>
    H.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1)
  have hAprod : ∀ y : V → ℝ, (∏ e ∈ H.edgeFinset \ T, P.edgeA y e)
      = ∏ v, P.f (y v) ^ ((H.edgeFinset \ T).filter fun e => v ∈ e).card := fun y =>
    prod_edges_subset_eq_prod_pow_card (H.edgeFinset \ T) hSnd fun v => P.f (y v)
  -- effect of re-randomising the `w`-coordinate
  have hEupd : ∀ (y : V → ℝ) (s : ℝ) (e : Sym2 V), w ∉ e →
      P.edgeE (Function.update y w s) e = P.edgeE y e := by
    intro y s e hwe
    revert hwe
    induction e using Sym2.ind with
    | _ p q =>
      intro hwe
      rw [Sym2.mem_iff] at hwe
      push Not at hwe
      show P.resid (Function.update y w s p) (Function.update y w s q) = P.resid (y p) (y q)
      rw [Function.update_of_ne (Ne.symm hwe.1), Function.update_of_ne (Ne.symm hwe.2)]
  have hTsplit : ∀ z : V → ℝ, (∏ e ∈ T, P.edgeE z e)
      = P.edgeE z e₀ * ∏ e ∈ T.erase e₀, P.edgeE z e := fun z =>
    (Finset.mul_prod_erase T _ he₀mem.1).symm
  have hVsplit : ∀ z : V → ℝ,
      (∏ v, P.f (z v) ^ ((H.edgeFinset \ T).filter fun e => v ∈ e).card)
      = P.f (z w) ^ (d - 1)
        * ∏ v ∈ Finset.univ.erase w,
            P.f (z v) ^ ((H.edgeFinset \ T).filter fun e => v ∈ e).card := by
    intro z
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), hSdeg]
  have hpt : ∀ (y : V → ℝ) (s : ℝ),
      (∏ e ∈ T, P.edgeE (Function.update y w s) e)
        * ∏ e ∈ H.edgeFinset \ T, P.edgeA (Function.update y w s) e
      = ((∏ e ∈ T.erase e₀, P.edgeE y e)
          * ∏ v ∈ Finset.univ.erase w,
              P.f (y v) ^ ((H.edgeFinset \ T).filter fun e => v ∈ e).card)
        * (P.resid (y (Sym2.Mem.other he₀mem.2)) s * P.f s ^ (d - 1)) := by
    intro y s
    have h1 : P.edgeE (Function.update y w s) e₀
        = P.resid (y (Sym2.Mem.other he₀mem.2)) s := by
      have hval : P.edgeE (Function.update y w s) s(w, Sym2.Mem.other he₀mem.2)
          = P.resid (y (Sym2.Mem.other he₀mem.2)) s := by
        show P.resid (Function.update y w s w)
            (Function.update y w s (Sym2.Mem.other he₀mem.2)) = _
        rw [Function.update_self, Function.update_of_ne huw]
        exact P.resid_symm _ _
      rwa [hspec] at hval
    have h2 : (∏ e ∈ T.erase e₀, P.edgeE (Function.update y w s) e)
        = ∏ e ∈ T.erase e₀, P.edgeE y e :=
      Finset.prod_congr rfl fun e he => hEupd y s e fun hwe =>
        (Finset.ne_of_mem_erase he) (huniq e (Finset.mem_of_mem_erase he) hwe)
    have h4 : (∏ v ∈ Finset.univ.erase w,
          P.f (Function.update y w s v) ^ ((H.edgeFinset \ T).filter fun e => v ∈ e).card)
        = ∏ v ∈ Finset.univ.erase w,
          P.f (y v) ^ ((H.edgeFinset \ T).filter fun e => v ∈ e).card :=
      Finset.prod_congr rfl fun v hv => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
    rw [hAprod, hTsplit, hVsplit, h1, h2, h4, Function.update_self]
    ring
  -- the inner integral vanishes almost everywhere
  have hortho : ∀ᵐ y ∂(Measure.pi fun _ : V => unitμ),
      (∫ s, P.resid (y (Sym2.Mem.other he₀mem.2)) s * P.f s ^ (d - 1) ∂unitμ) = 0 := by
    have hP : ∀ᵐ t ∂unitμ, (∫ s, P.resid t s * P.f s ^ (d - 1) ∂unitμ) = 0 := by
      filter_upwards [P.ortho] with t ht using ht
    exact (measurePreserving_eval (μ := fun _ : V => unitμ)
      (Sym2.Mem.other he₀mem.2)).quasiMeasurePreserving.ae hP
  have hzero : ∀ᵐ y ∂(Measure.pi fun _ : V => unitμ),
      (∫ s, (∏ e ∈ T, P.edgeE (Function.update y w s) e)
        * ∏ e ∈ H.edgeFinset \ T, P.edgeA (Function.update y w s) e ∂unitμ) = 0 := by
    filter_upwards [hortho] with y hy
    calc ∫ s, (∏ e ∈ T, P.edgeE (Function.update y w s) e)
          * ∏ e ∈ H.edgeFinset \ T, P.edgeA (Function.update y w s) e ∂unitμ
        = ∫ s, ((∏ e ∈ T.erase e₀, P.edgeE y e)
            * ∏ v ∈ Finset.univ.erase w,
                P.f (y v) ^ ((H.edgeFinset \ T).filter fun e => v ∈ e).card)
          * (P.resid (y (Sym2.Mem.other he₀mem.2)) s * P.f s ^ (d - 1)) ∂unitμ :=
          integral_congr_ae (Filter.Eventually.of_forall (hpt y))
      _ = ((∏ e ∈ T.erase e₀, P.edgeE y e)
            * ∏ v ∈ Finset.univ.erase w,
                P.f (y v) ^ ((H.edgeFinset \ T).filter fun e => v ∈ e).card)
          * ∫ s, P.resid (y (Sym2.Mem.other he₀mem.2)) s * P.f s ^ (d - 1) ∂unitμ :=
          integral_const_mul _ _
      _ = 0 := by rw [hy, mul_zero]
  rw [integral_pi_update w (P.measurable_termFun T (H.edgeFinset \ T))
    (C := 5 ^ H.edgeFinset.card * 4 ^ H.edgeFinset.card) (P.abs_termFun_le H hT)]
  exact integral_eq_zero_of_ae hzero

/-! ## The bound on a surviving term, and the assembly -/

/-- **Step (c): every nonempty term is `O(‖E‖₂³)`.**

If some vertex has residual degree one the term is zero; otherwise `exists_walk3` produces
three distinct residual edges forming a walk, the remaining residual factors are dropped at
cost `5` each and the rank-one factors at cost `4` each, and `walk3_bound` finishes. -/
theorem abs_integral_term_le {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) {T : Finset (Sym2 V)}
    (hT : T ⊆ H.edgeFinset) (hTne : T.Nonempty) :
    |∫ y : V → ℝ, (∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e
        ∂(Measure.pi fun _ : V => unitμ)|
      ≤ 4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card * P.residL2 ^ 3 := by
  classical
  have hL3 : (0:ℝ) ≤ P.residL2 ^ 3 := pow_nonneg P.residL2_nonneg 3
  by_cases hone : ∃ w : V, (T.filter fun e => w ∈ e).card = 1
  · obtain ⟨w, hw⟩ := hone
    rw [P.integral_term_eq_zero H hreg hT hw, abs_zero]
    have hpos : (0:ℝ) ≤ 4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card :=
      mul_nonneg (by positivity) (by positivity)
    exact mul_nonneg hpos hL3
  · push Not at hone
    obtain ⟨a, b, c, v, hab', hac', hbv', h01, h02, h12, hab, hca, hcb, hva, hvb⟩ :=
      exists_walk3 H hT hTne hone
    -- the three chosen edges
    set K : Finset (Sym2 V) := {s(a, b), s(a, c), s(b, v)} with hK
    have hKsub : K ⊆ T := by
      rw [hK]
      refine Finset.insert_subset hab' (Finset.insert_subset hac' ?_)
      simpa using hbv'
    have hKprod : ∀ y : V → ℝ, (∏ e ∈ K, |P.edgeE y e|)
        = |P.resid (y a) (y b)| * (|P.resid (y a) (y c)| * |P.resid (y b) (y v)|) := by
      intro y
      rw [hK, Finset.prod_insert (by simp [h01, h02]), Finset.prod_insert (by simp [h12]),
        Finset.prod_singleton]
      rfl
    -- the pointwise bound
    have hbdd : ∀ y : V → ℝ,
        |(∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e|
        ≤ 4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card
          * (|P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)|) := by
      intro y
      rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
      have hA : ∏ e ∈ H.edgeFinset \ T, |P.edgeA y e| ≤ 4 ^ H.edgeFinset.card := by
        calc ∏ e ∈ H.edgeFinset \ T, |P.edgeA y e| ≤ ∏ _e ∈ H.edgeFinset \ T, (4:ℝ) :=
              Finset.prod_le_prod (fun e _ => abs_nonneg _) fun e _ => P.abs_edgeA_le y e
          _ = 4 ^ (H.edgeFinset \ T).card := Finset.prod_const _
          _ ≤ 4 ^ H.edgeFinset.card :=
              pow_le_pow_right₀ (by norm_num) (Finset.card_le_card Finset.sdiff_subset)
      have hsplit : (∏ e ∈ T, |P.edgeE y e|)
          = (∏ e ∈ T \ K, |P.edgeE y e|) * ∏ e ∈ K, |P.edgeE y e| :=
        (Finset.prod_sdiff hKsub).symm
      have hdrop : ∏ e ∈ T \ K, |P.edgeE y e| ≤ 5 ^ H.edgeFinset.card := by
        calc ∏ e ∈ T \ K, |P.edgeE y e| ≤ ∏ _e ∈ T \ K, (5:ℝ) :=
              Finset.prod_le_prod (fun e _ => abs_nonneg _) fun e _ => P.abs_edgeE_le y e
          _ = 5 ^ (T \ K).card := Finset.prod_const _
          _ ≤ 5 ^ H.edgeFinset.card :=
              pow_le_pow_right₀ (by norm_num)
                (Finset.card_le_card (Finset.sdiff_subset.trans hT))
      have hEle : (∏ e ∈ T, |P.edgeE y e|)
          ≤ 5 ^ H.edgeFinset.card
            * (|P.resid (y a) (y b)| * (|P.resid (y a) (y c)| * |P.resid (y b) (y v)|)) := by
        rw [hsplit, hKprod y]
        exact mul_le_mul_of_nonneg_right hdrop (by positivity)
      have hAnn : (0:ℝ) ≤ ∏ e ∈ H.edgeFinset \ T, |P.edgeA y e| :=
        Finset.prod_nonneg fun e _ => abs_nonneg _
      have hEnn : (0:ℝ) ≤ ∏ e ∈ T, |P.edgeE y e| :=
        Finset.prod_nonneg fun e _ => abs_nonneg _
      nlinarith [hEle, hA, hAnn, hEnn, abs_nonneg (P.resid (y a) (y b)),
        abs_nonneg (P.resid (y a) (y c)), abs_nonneg (P.resid (y b) (y v))]
    -- integrate the pointwise bound
    have hmeasG : Measurable fun y : V → ℝ =>
        |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)| :=
      (((P.measurable_residAt a b).abs).mul ((P.measurable_residAt a c).abs)).mul
        ((P.measurable_residAt b v).abs)
    have hintG : Integrable (fun y : V → ℝ =>
        |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)|)
        (Measure.pi fun _ : V => unitμ) :=
      integrable_of_abs_le hmeasG 125 fun y => by
        have h12 : |P.resid (y a) (y b)| * |P.resid (y a) (y c)| ≤ 25 := by
          nlinarith [P.abs_resid_le (y a) (y b), P.abs_resid_le (y a) (y c),
            abs_nonneg (P.resid (y a) (y b)), abs_nonneg (P.resid (y a) (y c))]
        have h12nn : (0:ℝ) ≤ |P.resid (y a) (y b)| * |P.resid (y a) (y c)| :=
          mul_nonneg (abs_nonneg _) (abs_nonneg _)
        rw [abs_of_nonneg (mul_nonneg h12nn (abs_nonneg _))]
        nlinarith [h12, h12nn, P.abs_resid_le (y b) (y v),
          abs_nonneg (P.resid (y b) (y v))]
    have hintF : Integrable (fun y : V → ℝ =>
        |(∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e|)
        (Measure.pi fun _ : V => unitμ) :=
      (integrable_of_abs_le (P.measurable_termFun T (H.edgeFinset \ T))
        (5 ^ H.edgeFinset.card * 4 ^ H.edgeFinset.card)
        fun y => P.abs_termFun_le H hT y).abs
    calc |∫ y : V → ℝ, (∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e
            ∂(Measure.pi fun _ : V => unitμ)|
        ≤ ∫ y : V → ℝ, |(∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e|
            ∂(Measure.pi fun _ : V => unitμ) := abs_integral_le_integral_abs
      _ ≤ ∫ y : V → ℝ, 4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card
            * (|P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)|)
            ∂(Measure.pi fun _ : V => unitμ) :=
          integral_mono hintF (hintG.const_mul _) hbdd
      _ = 4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card
            * ∫ y : V → ℝ,
              |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)|
              ∂(Measure.pi fun _ : V => unitμ) := integral_const_mul _ _
      _ ≤ 4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card * P.residL2 ^ 3 :=
          mul_le_mul_of_nonneg_left (P.walk3_bound hab hca hcb hva hvb) (by positivity)

/-- **`eq:rank-one-reduction-bounds`**: for a `d`-regular `H` on `v` vertices
with `m` edges,

`|t(H, W) - q^v| ≤ 40^m ‖E‖₂³`.

The `T = ∅` term of `tDensity_expand` is `q^v` (`integral_edgeA_prod`), and each of the at
most `2^m` remaining terms is bounded by `4^m·5^m‖E‖₂³` (`abs_integral_term_le`). -/
theorem abs_tDensity_sub_qVal_pow_le {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) :
    |W.tDensity H - P.qVal ^ Fintype.card V|
      ≤ (40 : ℝ) ^ H.edgeFinset.card * P.residL2 ^ 3 := by
  classical
  have hmem : (∅ : Finset (Sym2 V)) ∈ H.edgeFinset.powerset := Finset.empty_mem_powerset _
  have hempty : ∫ y : V → ℝ, (∏ e ∈ (∅ : Finset (Sym2 V)), P.edgeE y e)
        * ∏ e ∈ H.edgeFinset \ (∅ : Finset (Sym2 V)), P.edgeA y e
        ∂(Measure.pi fun _ : V => unitμ) = P.qVal ^ Fintype.card V := by
    simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul]
    exact P.integral_edgeA_prod H hreg
  rw [P.tDensity_expand H, ← Finset.add_sum_erase _ _ hmem, hempty, add_sub_cancel_left]
  have hterm : ∀ T ∈ H.edgeFinset.powerset.erase ∅,
      |∫ y : V → ℝ, (∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e
          ∂(Measure.pi fun _ : V => unitμ)|
        ≤ 4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card * P.residL2 ^ 3 := by
    intro T hTmem
    have hTne : T.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hTmem)
    exact P.abs_integral_term_le H hreg
      (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hTmem)) hTne
  have hcard : ((H.edgeFinset.powerset.erase ∅).card : ℝ) ≤ 2 ^ H.edgeFinset.card := by
    have h1 : (H.edgeFinset.powerset.erase ∅).card ≤ 2 ^ H.edgeFinset.card := by
      calc (H.edgeFinset.powerset.erase ∅).card ≤ H.edgeFinset.powerset.card :=
            Finset.card_erase_le
        _ = 2 ^ H.edgeFinset.card := Finset.card_powerset _
    exact_mod_cast h1
  calc |∑ T ∈ H.edgeFinset.powerset.erase ∅,
          ∫ y : V → ℝ, (∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e
            ∂(Measure.pi fun _ : V => unitμ)|
      ≤ ∑ T ∈ H.edgeFinset.powerset.erase ∅,
          |∫ y : V → ℝ, (∏ e ∈ T, P.edgeE y e) * ∏ e ∈ H.edgeFinset \ T, P.edgeA y e
            ∂(Measure.pi fun _ : V => unitμ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (H.edgeFinset.powerset.erase ∅).card
          • (4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card * P.residL2 ^ 3) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((H.edgeFinset.powerset.erase ∅).card : ℝ)
          * (4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card * P.residL2 ^ 3) := by
        rw [nsmul_eq_mul]
    _ ≤ 2 ^ H.edgeFinset.card
          * (4 ^ H.edgeFinset.card * 5 ^ H.edgeFinset.card * P.residL2 ^ 3) :=
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (mul_nonneg (by positivity) (by positivity))
            (pow_nonneg P.residL2_nonneg 3))
    _ = (40 : ℝ) ^ H.edgeFinset.card * P.residL2 ^ 3 := by
        rw [show (40:ℝ) = 2 * 4 * 5 by norm_num, mul_pow, mul_pow]
        ring

/-- **`eq:rank-one-reduction-bounds` in the displayed form**:
`t(H, W) = q^v + R_H(f, E)` with `|R_H(f, E)| ≤ C‖E‖₂³` and `C = 40^{|E(H)|}` depending
only on `H`. -/
theorem tDensity_eq_qVal_pow_add {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = d) :
    ∃ R : ℝ, W.tDensity H = P.qVal ^ Fintype.card V + R
      ∧ |R| ≤ (40 : ℝ) ^ H.edgeFinset.card * P.residL2 ^ 3 :=
  ⟨W.tDensity H - P.qVal ^ Fintype.card V, by ring,
    P.abs_tDensity_sub_qVal_pow_le H hreg⟩

end FactorDecomp

end SingularEndpoint

end UpperTailOptimizers
