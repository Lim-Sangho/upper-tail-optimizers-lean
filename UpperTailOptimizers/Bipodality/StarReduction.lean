import UpperTailOptimizers.Bipodality.StarTerms
import UpperTailOptimizers.KRRS.Reduced

/-!
# The star reduction of the homomorphism density

For a `d`-regular graph `H` with `v` vertices and `m` edges and a graphon `W` of edge density
`ε`, write `δW = W - ε` and `d_W(x) = ∫ W(x,y) dy`.  Then (draft `kb:lem:star`)

  `|t(H,W) - ε^m - v ε^{m-d} ∫ 𝒟_ε(d_W(x)) dx| ≤ 10^m ‖δW‖₂³`.

Expanding `∏_e (ε + δW_e)` gives one term per edge set `T ⊆ E(H)`.  A star with `j ≥ 2` edges
integrates to `∫ (d_W - ε)^j`, and summing over the `v` centres and the `C(d,j)` stars of each
size reassembles `v ε^{m-d} ∫ 𝒟_ε(d_W)`.  Every other nonempty `T` either has an isolated edge,
and vanishes because `∬ δW = 0`, or contains a three-edge walk or two edges at a vertex plus a
disjoint edge, and is `O(‖δW‖₂³)`.

## Contents

* `devKernel` — `W - ε` as a bounded symmetric kernel; `Graphon.degFun` — the degree function;
* `tDensity_expand_const` — the expansion over edge sets;
* `starTerm`, `abs_integral_sub_starTerm_le` — the per-term estimate;
* `sum_starTerm` — the star terms reassemble `v ε^{m-d} ∫ 𝒟_ε(d_W)`;
* **`abs_tDensity_sub_star_le`** — the star reduction.
-/

namespace UpperTailOptimizers

open MeasureTheory SingularEndpoint

/-- `W - ε` as a bounded symmetric kernel. -/
noncomputable def devKernel (W : Graphon) (ε : ℝ) (hε : ε ∈ Set.Icc (0:ℝ) 1) : BKernel where
  E x y := W.toFun x y - ε
  meas := W.measurable_uncurry.sub measurable_const
  bound x y := by
    have h := W.mem_Icc x y
    rw [abs_le]
    constructor <;> linarith [h.1, h.2, hε.1, hε.2]
  symm' x y := by rw [W.symm' x y]

namespace Graphon

/-- The degree function `d_W(x) = ∫ W(x,y) dy`. -/
noncomputable def degFun (W : Graphon) (x : ℝ) : ℝ := ∫ y, W.toFun x y ∂unitμ

theorem integrable_row (W : Graphon) (x : ℝ) : Integrable (fun y => W.toFun x y) unitμ :=
  integrable_of_abs_le (measurable_toFun_right W x) 1 fun y => by
    rw [abs_of_nonneg (W.nonneg' x y)]; exact W.le_one' x y

theorem measurable_degFun (W : Graphon) : Measurable W.degFun :=
  (W.measurable_uncurry.stronglyMeasurable).integral_prod_right'.measurable

theorem degFun_mem_Icc (W : Graphon) (x : ℝ) : W.degFun x ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨integral_nonneg fun y => W.nonneg' x y, ?_⟩
  have h := integral_mono (W.integrable_row x) (integrable_const (1:ℝ)) fun y => W.le_one' x y
  simpa [degFun] using h

/-- `∫ d_W = e(W)`. -/
theorem integral_degFun (W : Graphon) : ∫ x, W.degFun x ∂unitμ = W.edgeDensity :=
  integral_integral W.integrable_self

end Graphon

theorem degFun_eq_add_rowInt (W : Graphon) {ε : ℝ} (hε : ε ∈ Set.Icc (0:ℝ) 1) (x : ℝ) :
    W.degFun x = ε + (devKernel W ε hε).rowInt x := by
  show ∫ y, W.toFun x y ∂unitμ = ε + ∫ y, (W.toFun x y - ε) ∂unitμ
  rw [integral_sub (W.integrable_row x) (integrable_const ε)]
  simp

theorem integral_devKernel (W : Graphon) {ε : ℝ} (hε : ε ∈ Set.Icc (0:ℝ) 1)
    (he : W.edgeDensity = ε) : ∫ z, (devKernel W ε hε).E z.1 z.2 ∂gμ = 0 := by
  show ∫ z, (W.toFun z.1 z.2 - ε) ∂gμ = 0
  rw [integral_sub W.integrable_self (integrable_const ε)]
  simp only [integral_const, smul_eq_mul]
  rw [show ∫ z, W.toFun z.1 z.2 ∂gμ = W.edgeDensity from rfl, he]
  simp [gμ, measureReal_def]

theorem devKernel_residSq (W : Graphon) {ε : ℝ} (hε : ε ∈ Set.Icc (0:ℝ) 1) :
    (devKernel W ε hε).residSq = ∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ := rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The expansion around a constant**:
`t(H,W) = ∑_{T ⊆ E(H)} ε^{m-|T|} ∫ ∏_{e ∈ T} (W - ε)_e`. -/
theorem tDensity_expand_const (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) 1) :
    W.tDensity H = ∑ T ∈ H.edgeFinset.powerset,
      ε ^ (H.edgeFinset.card - T.card)
        * ∫ y : V → ℝ, ∏ e ∈ T, (devKernel W ε hε).kEdge y e ∂(Measure.pi fun _ : V => unitμ) := by
  classical
  set P := devKernel W ε hε with hP
  have hpt : ∀ y : V → ℝ,
      (∏ e ∈ H.edgeFinset, Sym2.lift ⟨fun a b => W.toFun (y a) (y b),
          fun a b => W.symm' (y a) (y b)⟩ e)
      = ∑ T ∈ H.edgeFinset.powerset,
          ε ^ (H.edgeFinset.card - T.card) * ∏ e ∈ T, P.kEdge y e := by
    intro y
    have hfac : ∀ e : Sym2 V, Sym2.lift ⟨fun a b => W.toFun (y a) (y b),
        fun a b => W.symm' (y a) (y b)⟩ e = P.kEdge y e + ε := by
      intro e
      induction e using Sym2.ind with
      | _ p q =>
        show W.toFun (y p) (y q) = (W.toFun (y p) (y q) - ε) + ε
        ring
    rw [Finset.prod_congr rfl fun e _ => hfac e, Finset.prod_add]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hT)]
    ring
  have hint : ∀ T ∈ H.edgeFinset.powerset, Integrable (fun y : V → ℝ =>
      ε ^ (H.edgeFinset.card - T.card) * ∏ e ∈ T, P.kEdge y e)
      (Measure.pi fun _ : V => unitμ) := fun T _ =>
    (integrable_of_abs_le (P.measurable_prod_kEdge T) (5 ^ T.card)
      fun y => P.abs_prod_kEdge_le T y).const_mul _
  show ∫ y : V → ℝ, _ ∂(Measure.pi fun _ : V => unitμ) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum _ hint]
  exact Finset.sum_congr rfl fun T _ => integral_const_mul _ _

namespace BKernel

variable (P : BKernel)

/-- The star part of the term indexed by `T`: `∫ δ^{|T|}` if `T` is a star with at least two
edges (its centre is then unique), and `0` otherwise. -/
noncomputable def starTerm (H : SimpleGraph V) [DecidableRel H.Adj] (T : Finset (Sym2 V)) : ℝ :=
  ∑ u : V, if 2 ≤ T.card ∧ T ⊆ H.incidenceFinset u then ∫ t, P.rowInt t ^ T.card ∂unitμ else 0

/-- Dropping all but a few factors: `|∫ ∏_T E| ≤ 5^{|T|} ∫ ∏_K |E|` for `K ⊆ T`. -/
theorem abs_integral_prod_le_of_subset {T K : Finset (Sym2 V)} (hK : K ⊆ T) :
    |∫ y : V → ℝ, ∏ e ∈ T, P.kEdge y e ∂(Measure.pi fun _ : V => unitμ)|
      ≤ 5 ^ T.card * ∫ y : V → ℝ, ∏ e ∈ K, |P.kEdge y e| ∂(Measure.pi fun _ : V => unitμ) := by
  have hmeasK : Measurable fun y : V → ℝ => ∏ e ∈ K, |P.kEdge y e| :=
    Finset.measurable_prod _ fun e _ => (P.measurable_kEdge e).abs
  have hintK : Integrable (fun y : V → ℝ => ∏ e ∈ K, |P.kEdge y e|)
      (Measure.pi fun _ : V => unitμ) :=
    integrable_of_abs_le hmeasK (5 ^ K.card) fun y => by
      rw [abs_of_nonneg (Finset.prod_nonneg fun e _ => abs_nonneg _), ← Finset.abs_prod]
      exact P.abs_prod_kEdge_le K y
  have hintT : Integrable (fun y : V → ℝ => |∏ e ∈ T, P.kEdge y e|)
      (Measure.pi fun _ : V => unitμ) :=
    (integrable_of_abs_le (P.measurable_prod_kEdge T) (5 ^ T.card)
      fun y => P.abs_prod_kEdge_le T y).abs
  have hpt : ∀ y : V → ℝ, |∏ e ∈ T, P.kEdge y e| ≤ 5 ^ T.card * ∏ e ∈ K, |P.kEdge y e| := by
    intro y
    rw [Finset.abs_prod, ← Finset.prod_sdiff hK]
    have h1 : ∏ e ∈ T \ K, |P.kEdge y e| ≤ 5 ^ T.card := by
      calc ∏ e ∈ T \ K, |P.kEdge y e| ≤ ∏ _e ∈ T \ K, (5:ℝ) :=
            Finset.prod_le_prod (fun e _ => abs_nonneg _) fun e _ => P.abs_kEdge_le y e
        _ = 5 ^ (T \ K).card := Finset.prod_const _
        _ ≤ 5 ^ T.card := pow_le_pow_right₀ (by norm_num) (Finset.card_le_card Finset.sdiff_subset)
    exact mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun e _ => abs_nonneg _)
  calc |∫ y : V → ℝ, ∏ e ∈ T, P.kEdge y e ∂(Measure.pi fun _ : V => unitμ)|
      ≤ ∫ y : V → ℝ, |∏ e ∈ T, P.kEdge y e| ∂(Measure.pi fun _ : V => unitμ) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y : V → ℝ, 5 ^ T.card * ∏ e ∈ K, |P.kEdge y e| ∂(Measure.pi fun _ : V => unitμ) :=
        integral_mono hintT (hintK.const_mul _) hpt
    _ = 5 ^ T.card * ∫ y : V → ℝ, ∏ e ∈ K, |P.kEdge y e| ∂(Measure.pi fun _ : V => unitμ) :=
        integral_const_mul _ _

/-- The centre of a star with at least two edges is unique. -/
theorem center_unique (H : SimpleGraph V) [DecidableRel H.Adj] {T : Finset (Sym2 V)}
    (hT2 : 2 ≤ T.card) {u u' : V} (hu : T ⊆ H.incidenceFinset u)
    (hu' : T ⊆ H.incidenceFinset u') : u = u' := by
  classical
  by_contra hne
  obtain ⟨e₁, he₁, e₂, he₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  have hmem : ∀ e ∈ T, e = s(u, u') := by
    intro e he
    have h1 := (SimpleGraph.mem_incidenceFinset H u e).mp (hu he)
    have h2 := (SimpleGraph.mem_incidenceFinset H u' e).mp (hu' he)
    exact (Sym2.mem_and_mem_iff hne).mp ⟨h1.2, h2.2⟩
  exact h12 ((hmem e₁ he₁).trans (hmem e₂ he₂).symm)

/-- **The per-term estimate.**  For a nonempty `T ⊆ E(H)` and a kernel with `∬ E = 0`, the
term `∫ ∏_T E` differs from its star part by at most `5^{|T|} ‖E‖₂³`. -/
theorem abs_integral_sub_starTerm_le (H : SimpleGraph V) [DecidableRel H.Adj]
    {T : Finset (Sym2 V)} (hT : T ⊆ H.edgeFinset) (hTne : T.Nonempty)
    (hzero : ∫ z, P.E z.1 z.2 ∂gμ = 0) :
    |∫ y : V → ℝ, ∏ e ∈ T, P.kEdge y e ∂(Measure.pi fun _ : V => unitμ) - P.starTerm H T|
      ≤ 5 ^ T.card * P.residL2 ^ 3 := by
  classical
  have hL3 : 0 ≤ P.residL2 ^ 3 := pow_nonneg P.residL2_nonneg 3
  have h5 : (0:ℝ) ≤ 5 ^ T.card := by positivity
  by_cases hstar : ∃ u, 2 ≤ T.card ∧ T ⊆ H.incidenceFinset u
  · obtain ⟨u, hT2, hTu⟩ := hstar
    have hS : P.starTerm H T = ∫ t, P.rowInt t ^ T.card ∂unitμ := by
      unfold starTerm
      rw [Finset.sum_eq_single u]
      · rw [if_pos ⟨hT2, hTu⟩]
      · intro u' _ hu'
        rw [if_neg]
        rintro ⟨-, hTu'⟩
        exact hu' (center_unique H hT2 hTu' hTu)
      · intro h
        exact absurd (Finset.mem_univ u) h
    have hTstar : ∀ e ∈ T, ∃ w, w ≠ u ∧ e = s(u, w) := by
      intro e he
      have hinc := (SimpleGraph.mem_incidenceFinset H u e).mp (hTu he)
      have hnd : ¬ e.IsDiag := H.not_isDiag_of_mem_edgeSet hinc.1
      exact ⟨Sym2.Mem.other hinc.2, Sym2.other_ne hnd hinc.2, (Sym2.other_spec hinc.2).symm⟩
    have hI : ∫ y : V → ℝ, ∏ e ∈ T, P.kEdge y e ∂(Measure.pi fun _ : V => unitμ)
        = ∫ t, P.rowInt t ^ T.card ∂unitμ := by
      have h := P.integral_star u T hTstar (G := fun _ => (1:ℝ)) measurable_const (CG := 1)
        (fun _ => by simp)
      simpa using h
    rw [hI, hS, sub_self, abs_zero]
    positivity
  · have hS : P.starTerm H T = 0 := by
      unfold starTerm
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [if_neg]
      rintro ⟨h2, hu⟩
      exact hstar ⟨u, h2, hu⟩
    rw [hS, sub_zero]
    rcases exists_star_structure H hT hTne with ⟨a, b, hab, habT, hiso⟩ | ⟨u, hT2, hTu⟩ |
        ⟨a, b, c, v, hab', hac', hbv', h01, h02, h12, hab, hca, hcb, hva, hvb⟩ |
        ⟨a, b, c, x, z, hab', hac', hxz', hab, hac, hbc, hxz, hxa, hxb, hxc, hza, hzb, hzc⟩
    · rw [P.integral_isolated_edge T hab habT hiso hzero, abs_zero]
      positivity
    · exfalso
      apply hstar
      refine ⟨u, hT2, fun e he => ?_⟩
      obtain ⟨w, -, rfl⟩ := hTu e he
      exact (SimpleGraph.mem_incidenceFinset H u _).mpr
        ⟨SimpleGraph.mem_edgeFinset.mp (hT he), Sym2.mem_mk_left u w⟩
    · set K : Finset (Sym2 V) := {s(a, b), s(a, c), s(b, v)} with hK
      have hKsub : K ⊆ T := by
        rw [hK]
        refine Finset.insert_subset hab' (Finset.insert_subset hac' ?_)
        simpa using hbv'
      have hKprod : ∀ y : V → ℝ, ∏ e ∈ K, |P.kEdge y e|
          = |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y b) (y v)| := by
        intro y
        rw [hK, Finset.prod_insert (by simp [h01, h02]), Finset.prod_insert (by simp [h12]),
          Finset.prod_singleton]
        simp only [kEdge_mk, resid]
        ring
      refine le_trans (P.abs_integral_prod_le_of_subset hKsub) ?_
      rw [integral_congr_ae (Filter.Eventually.of_forall hKprod)]
      exact mul_le_mul_of_nonneg_left (P.walk3_bound hab hca hcb hva hvb) h5
    · have hne1 : s(a, b) ≠ s(a, c) := fun h => hbc (Sym2.congr_right.mp h)
      have hne2 : s(a, b) ≠ s(x, z) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hxa h1.symm
        · exact hza h1.symm
      have hne3 : s(a, c) ≠ s(x, z) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hxa h1.symm
        · exact hza h1.symm
      set K : Finset (Sym2 V) := {s(a, b), s(a, c), s(x, z)} with hK
      have hKsub : K ⊆ T := by
        rw [hK]
        refine Finset.insert_subset hab' (Finset.insert_subset hac' ?_)
        simpa using hxz'
      have hKprod : ∀ y : V → ℝ, ∏ e ∈ K, |P.kEdge y e|
          = |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y x) (y z)| := by
        intro y
        rw [hK, Finset.prod_insert (by simp [hne1, hne2]), Finset.prod_insert (by simp [hne3]),
          Finset.prod_singleton]
        simp only [kEdge_mk, resid]
        ring
      refine le_trans (P.abs_integral_prod_le_of_subset hKsub) ?_
      rw [integral_congr_ae (Filter.Eventually.of_forall hKprod)]
      exact mul_le_mul_of_nonneg_left
        (P.cherry_edge_bound hab hac hbc hxz hxa hxb hxc hza hzb hzc) h5

/-- **The star terms reassemble by size.**  Each vertex is the centre of `C(d,j)` stars with
`j` edges. -/
theorem sum_starTerm (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ}
    (hreg : ∀ v, H.degree v = d) (ε : ℝ) :
    ∑ T ∈ H.edgeFinset.powerset, ε ^ (H.edgeFinset.card - T.card) * P.starTerm H T
      = (Fintype.card V : ℝ) * ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ)
          * (if 2 ≤ j then ε ^ (H.edgeFinset.card - j) * ∫ t, P.rowInt t ^ j ∂unitμ else 0) := by
  classical
  set g : ℕ → ℝ := fun j =>
    if 2 ≤ j then ε ^ (H.edgeFinset.card - j) * ∫ t, P.rowInt t ^ j ∂unitμ else 0 with hg
  have hswap : ∑ T ∈ H.edgeFinset.powerset, ε ^ (H.edgeFinset.card - T.card) * P.starTerm H T
      = ∑ u : V, ∑ T ∈ H.edgeFinset.powerset,
          if T ⊆ H.incidenceFinset u then g T.card else 0 := by
    unfold starTerm
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun T _ => ?_
    by_cases hsub : T ⊆ H.incidenceFinset u
    · by_cases h2 : 2 ≤ T.card
      · simp [hg, hsub, h2]
      · simp [hg, hsub, h2]
    · simp [hsub]
  have hvert : ∀ u : V, (∑ T ∈ H.edgeFinset.powerset,
      if T ⊆ H.incidenceFinset u then g T.card else 0)
      = ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * g j := by
    intro u
    rw [← Finset.sum_filter]
    have hfil : (H.edgeFinset.powerset.filter fun T => T ⊆ H.incidenceFinset u)
        = (H.incidenceFinset u).powerset := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨h.trans (H.incidenceFinset_subset u), h⟩⟩
    rw [hfil, Finset.sum_powerset_apply_card, SimpleGraph.card_incidenceFinset_eq_degree, hreg]
    simp only [nsmul_eq_mul]
  rw [hswap, Finset.sum_congr rfl fun u _ => hvert u, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

end BKernel

/-- The binomial expansion of `𝒟_ε(ε + δ)`: only the powers `δ^j` with `j ≥ 2` survive. -/
theorem Dfun_add_eq_sum {d : ℕ} (hd : 2 ≤ d) (ε δ : ℝ) :
    Dfun d ε (ε + δ) = ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ)
      * (if 2 ≤ j then ε ^ (d - j) * δ ^ j else 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hsplit : ∀ f : ℕ → ℝ, ∑ j ∈ Finset.range (k + 2 + 1), f j
      = ∑ j ∈ Finset.range (k + 1), f (j + 1 + 1) + f 1 + f 0 := by
    intro f
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
  unfold Dfun
  rw [add_comm ε δ, add_pow, hsplit, hsplit]
  have hsum : ∑ j ∈ Finset.range (k + 1), δ ^ (j + 1 + 1) * ε ^ (k + 2 - (j + 1 + 1))
        * ((k + 2).choose (j + 1 + 1) : ℝ)
      = ∑ j ∈ Finset.range (k + 1), ((k + 2).choose (j + 1 + 1) : ℝ)
        * (if 2 ≤ j + 1 + 1 then ε ^ (k + 2 - (j + 1 + 1)) * δ ^ (j + 1 + 1) else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos (by omega)]
    ring
  rw [hsum]
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one,
    Nat.choose_one_right, pow_one, show ¬ (2 ≤ 1) by omega, show ¬ (2 ≤ 0) by omega,
    if_false, mul_zero, add_zero, show k + 2 - 1 = k + 1 by omega, Nat.sub_zero]
  push_cast
  ring

/-- **The star reduction** (draft `kb:lem:star`): for `d`-regular `H` and `e(W) = ε`,

`|t(H,W) - ε^m - v ε^{m-d} ∫ 𝒟_ε(d_W)| ≤ 10^m ‖W - ε‖₂³`. -/
theorem abs_tDensity_sub_star_le (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (W : Graphon) {ε : ℝ} (hε : ε ∈ Set.Icc (0:ℝ) 1)
    (he : W.edgeDensity = ε) :
    |W.tDensity H - ε ^ H.edgeFinset.card
        - (Fintype.card V : ℝ) * ε ^ (H.edgeFinset.card - d) * ∫ x, Dfun d ε (W.degFun x) ∂unitμ|
      ≤ 10 ^ H.edgeFinset.card * Real.sqrt (∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ) ^ 3 := by
  classical
  set P := devKernel W ε hε with hP
  set m := H.edgeFinset.card with hm
  have hzero := integral_devKernel W hε he
  have hL : Real.sqrt (∫ z, (W.toFun z.1 z.2 - ε) ^ 2 ∂gμ) = P.residL2 := rfl
  rw [hL]
  -- the main term is the sum of the star parts
  have hD : ∫ x, Dfun d ε (W.degFun x) ∂unitμ = ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ)
      * (if 2 ≤ j then ε ^ (d - j) * ∫ t, P.rowInt t ^ j ∂unitμ else 0) := by
    have hpt : ∀ x, Dfun d ε (W.degFun x) = ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ)
        * (if 2 ≤ j then ε ^ (d - j) * P.rowInt x ^ j else 0) := fun x => by
      rw [degFun_eq_add_rowInt W hε x, Dfun_add_eq_sum hd]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
      split_ifs
      · rw [integral_const_mul]
      · simp
    · intro j _
      refine Integrable.const_mul ?_ _
      split_ifs
      · refine Integrable.const_mul ?_ _
        exact integrable_of_abs_le (P.measurable_rowInt.pow_const j) (5 ^ j) fun x => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (P.abs_rowInt_le x) j
      · exact integrable_zero _ _ _
  have hmain : (Fintype.card V : ℝ) * ε ^ (m - d) * ∫ x, Dfun d ε (W.degFun x) ∂unitμ
      = ∑ T ∈ H.edgeFinset.powerset, ε ^ (m - T.card) * P.starTerm H T := by
    rw [P.sum_starTerm H hreg ε, hD, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    split_ifs with h2
    · by_cases hV : (Fintype.card V : ℝ) = 0
      · simp [hV]
      · obtain ⟨u⟩ : Nonempty V := by
          rw [← Fintype.card_pos_iff]
          exact Nat.pos_of_ne_zero fun h => hV (by rw [h]; simp)
        have hdm : d ≤ m := by
          rw [← hreg u, ← SimpleGraph.card_incidenceFinset_eq_degree]
          exact Finset.card_le_card (H.incidenceFinset_subset u)
        have hpow : ε ^ (m - j) = ε ^ (m - d) * ε ^ (d - j) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hpow]
        ring
    · simp
  rw [tDensity_expand_const H W hε, ← hm, ← hP, hmain, sub_sub, add_comm (ε ^ m), ← sub_sub,
    ← Finset.sum_sub_distrib]
  have hmem : (∅ : Finset (Sym2 V)) ∈ H.edgeFinset.powerset := Finset.empty_mem_powerset _
  rw [← Finset.add_sum_erase _ _ hmem]
  have hS0 : P.starTerm H ∅ = 0 := by
    unfold BKernel.starTerm
    simp
  simp only [Finset.prod_empty, integral_const, Finset.card_empty, Nat.sub_zero, hS0, mul_zero,
    sub_zero, probReal_univ, smul_eq_mul, mul_one, add_sub_cancel_left]
  -- the remaining terms
  have hterm : ∀ T ∈ H.edgeFinset.powerset.erase ∅,
      |ε ^ (m - T.card) * (∫ y : V → ℝ, ∏ e ∈ T, P.kEdge y e ∂(Measure.pi fun _ : V => unitμ))
        - ε ^ (m - T.card) * P.starTerm H T| ≤ 5 ^ m * P.residL2 ^ 3 := by
    intro T hT
    have hTsub : T ⊆ H.edgeFinset := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT)
    have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hT)
    rw [← mul_sub, abs_mul]
    have h1 : |ε ^ (m - T.card)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hε.1 _)]
      exact pow_le_one₀ hε.1 hε.2
    have h2 := P.abs_integral_sub_starTerm_le H hTsub hTne hzero
    have h3 : (5:ℝ) ^ T.card * P.residL2 ^ 3 ≤ 5 ^ m * P.residL2 ^ 3 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hTsub))
        (pow_nonneg P.residL2_nonneg 3)
    calc |ε ^ (m - T.card)| * |(∫ y : V → ℝ, ∏ e ∈ T, P.kEdge y e
            ∂(Measure.pi fun _ : V => unitμ)) - P.starTerm H T|
        ≤ 1 * (5 ^ m * P.residL2 ^ 3) :=
          mul_le_mul h1 (h2.trans h3) (abs_nonneg _) zero_le_one
      _ = 5 ^ m * P.residL2 ^ 3 := one_mul _
  have hcard : ((H.edgeFinset.powerset.erase ∅).card : ℝ) ≤ 2 ^ m := by
    have h1 : (H.edgeFinset.powerset.erase ∅).card ≤ 2 ^ m :=
      (Finset.card_erase_le).trans (Finset.card_powerset _).le
    exact_mod_cast h1
  calc |∑ T ∈ H.edgeFinset.powerset.erase ∅,
        (ε ^ (m - T.card) * (∫ y : V → ℝ, ∏ e ∈ T, P.kEdge y e ∂(Measure.pi fun _ : V => unitμ))
          - ε ^ (m - T.card) * P.starTerm H T)|
      ≤ ∑ T ∈ H.edgeFinset.powerset.erase ∅,
        |ε ^ (m - T.card) * (∫ y : V → ℝ, ∏ e ∈ T, P.kEdge y e ∂(Measure.pi fun _ : V => unitμ))
          - ε ^ (m - T.card) * P.starTerm H T| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (H.edgeFinset.powerset.erase ∅).card • (5 ^ m * P.residL2 ^ 3) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((H.edgeFinset.powerset.erase ∅).card : ℝ) * (5 ^ m * P.residL2 ^ 3) := by
        rw [nsmul_eq_mul]
    _ ≤ 2 ^ m * (5 ^ m * P.residL2 ^ 3) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (by positivity) (pow_nonneg P.residL2_nonneg 3))
    _ = 10 ^ m * P.residL2 ^ 3 := by
        rw [show (10:ℝ) = 2 * 5 by norm_num, mul_pow]
        ring

end UpperTailOptimizers
