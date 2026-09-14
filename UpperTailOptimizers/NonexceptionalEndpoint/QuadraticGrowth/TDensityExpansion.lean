import UpperTailOptimizers.Preliminaries.Graphons.BipodalBridge
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.PowBounds

/-!
# The bipodal `H`-density polynomial and its small-block expansion

For the two-block bipodal graphon `V_{r,c,q}` in the proof of `lem:bipodal-quadratic-bound`
(block `A = [0,c]`, densities `a` on `A×A`, `s` across, `q` on `Aᶜ×Aᶜ`), the
homomorphism density `t(H, ·)` is the polynomial

`tBip H a s q c = ∑_{τ : V → Bool} (∏_{e ∈ E(H)} B(τ)) · c^{k(τ)} (1-c)^{n-k(τ)}`,

the sum over block labellings of the vertices, where `k(τ)` counts the vertices in
the small block (`bipodalGraphon_tDensity_sum` of `Preliminaries/Graphons/BipodalBridge.lean`
supplies the measure-theoretic bridge `tBip_eq_tDensity`).

The key structural fact for the quadratic upper bound is the **small-block
expansion** (`tBip_expansion`): for a `d`-regular `H`,

`tBip H a s q c = (1-c)^n q^m + n c (1-c)^{n-1} s^d q^{m-d} + tBipRem`,

where the labellings with at least two marked vertices contribute
`0 ≤ tBipRem ≤ 2^n c²` (`tBipRem_nonneg`, `tBipRem_le`).  Continuity of
`(q,c) ↦ tBip` (`continuous_tBip`) feeds the intermediate value theorem in
`BipodalUpper.lean`.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Finset

/-- The number of vertices assigned to the small block by a labelling. -/
def trueCount {V : Type*} [Fintype V] (τ : V → Bool) : ℕ :=
  (Finset.univ.filter fun v => τ v = true).card

/-- The edge factor of a labelling: the product over `E(H)` of the block values. -/
noncomputable def edgeProd {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q : ℝ) (τ : V → Bool) : ℝ :=
  ∏ e ∈ H.edgeFinset, Sym2.lift
    ⟨fun x y => blockVal a s q (τ x) (τ y),
      fun x y => blockVal_symm a s q (τ x) (τ y)⟩ e

/-- **The bipodal `H`-density polynomial** in the block size `c` and the large-block
density `q` (the small-block density is `a`, the cross density `s`). -/
noncomputable def tBip {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q c : ℝ) : ℝ :=
  ∑ τ : V → Bool, edgeProd H a s q τ
    * (c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ))

/-- **The remainder of the small-block expansion**: the contribution of the labellings
with at least two vertices in the small block. -/
noncomputable def tBipRem {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q c : ℝ) : ℝ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ), edgeProd H a s q τ
    * (c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ))

/-! ### Elementary facts about block values, edge factors, and labellings -/

/-- Each block value of the bipodal kernel lies in `[0,1]` when the three block
parameters do. -/
theorem blockVal_mem_Icc {a s q : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hq : q ∈ Set.Icc (0:ℝ) 1) (i j : Bool) : blockVal a s q i j ∈ Set.Icc (0:ℝ) 1 := by
  cases i <;> cases j <;> first | exact hq | exact hs | exact ha

/-- The edge product over any labelling lies in `[0,1]` when the block values do. -/
theorem edgeProd_mem_Icc {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {a s q : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hq : q ∈ Set.Icc (0:ℝ) 1) (τ : V → Bool) : edgeProd H a s q τ ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · refine Finset.prod_nonneg fun e _ => ?_
    induction e using Sym2.ind with
    | _ x y => exact (blockVal_mem_Icc ha hs hq (τ x) (τ y)).1
  · refine Finset.prod_le_one (fun e _ => ?_) (fun e _ => ?_)
    · induction e using Sym2.ind with
      | _ x y => exact (blockVal_mem_Icc ha hs hq (τ x) (τ y)).1
    · induction e using Sym2.ind with
      | _ x y => exact (blockVal_mem_Icc ha hs hq (τ x) (τ y)).2

/-- The all-`false` labelling has edge factor `q^m`. -/
theorem edgeProd_const_false {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q : ℝ) :
    edgeProd H a s q (fun _ => false) = q ^ H.edgeFinset.card := by
  refine Finset.prod_eq_pow_card fun e _ => ?_
  induction e using Sym2.ind with
  | _ x y => rfl

/-- The single-vertex labelling `τ = 1_{v₀}` has edge factor `s^{deg v₀} q^{m - deg v₀}`:
edges at `v₀` see the cross density, all others the large-block density. -/
theorem edgeProd_single {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s q : ℝ) (v₀ : V) :
    edgeProd H a s q (fun v => decide (v = v₀))
      = s ^ (H.degree v₀) * q ^ (H.edgeFinset.card - H.degree v₀) := by
  classical
  have hpt : ∀ e ∈ H.edgeFinset,
      Sym2.lift ⟨fun x y => blockVal a s q (decide (x = v₀)) (decide (y = v₀)),
        fun x y => blockVal_symm a s q (decide (x = v₀)) (decide (y = v₀))⟩ e
      = if v₀ ∈ e then s else q := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hadj : H.Adj x y := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hxy : x ≠ y := hadj.ne
      by_cases hx : x = v₀ <;> by_cases hy : y = v₀
      · exact absurd (hx.trans hy.symm) hxy
      · have hy' : ¬ v₀ = y := fun h => hy h.symm
        simp [blockVal, hx, hy, hy', Sym2.mem_iff]
      · have hx' : ¬ v₀ = x := fun h => hx h.symm
        simp [blockVal, hx, hy, hx', Sym2.mem_iff]
      · have hx' : ¬ v₀ = x := fun h => hx h.symm
        have hy' : ¬ v₀ = y := fun h => hy h.symm
        simp [blockVal, hx, hy, hx', hy', Sym2.mem_iff]
  rw [edgeProd, Finset.prod_congr rfl hpt, Finset.prod_ite _ _]
  rw [Finset.prod_const, Finset.prod_const]
  have hcard : (H.edgeFinset.filter fun e => v₀ ∈ e).card = H.degree v₀ := by
    rw [show (H.edgeFinset.filter fun e => v₀ ∈ e) = H.incidenceFinset v₀ from
      (H.incidenceFinset_eq_filter v₀).symm, SimpleGraph.card_incidenceFinset_eq_degree]
  have hcard' : (H.edgeFinset.filter fun e => ¬ v₀ ∈ e).card
      = H.edgeFinset.card - H.degree v₀ := by
    have := Finset.card_filter_add_card_filter_not
      (s := H.edgeFinset) (fun e => v₀ ∈ e)
    omega
  rw [hcard, hcard']

/-- A labelling with no marked vertex is the all-`false` labelling. -/
theorem label_eq_const_false {V : Type*} [Fintype V] {τ : V → Bool} (h : trueCount τ = 0) :
    τ = fun _ => false := by
  funext v
  by_contra hv
  have hτv : τ v = true := by
    revert hv; cases τ v <;> simp
  have hmem : v ∈ Finset.univ.filter fun v => τ v = true :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, hτv⟩
  rw [trueCount, Finset.card_eq_zero] at h
  rw [h] at hmem
  exact absurd hmem (Finset.notMem_empty v)

/-- A labelling with exactly one marked vertex is a single-vertex indicator. -/
theorem label_eq_single {V : Type*} [Fintype V] [DecidableEq V] {τ : V → Bool}
    (h : trueCount τ = 1) : ∃ v₀ : V, τ = fun v => decide (v = v₀) := by
  obtain ⟨v₀, hv₀⟩ := Finset.card_eq_one.mp h
  refine ⟨v₀, funext fun v => ?_⟩
  by_cases hvv : v = v₀
  · subst hvv
    have hmem : v ∈ Finset.univ.filter fun w => τ w = true := by
      rw [hv₀]; exact Finset.mem_singleton_self v
    have hτ : τ v = true := (Finset.mem_filter.mp hmem).2
    simp [hτ]
  · have hnot : v ∉ Finset.univ.filter fun w => τ w = true := by
      rw [hv₀]; simpa using hvv
    have hτ : τ v = false := by
      have hne := fun hτv => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hτv⟩)
      revert hne; cases τ v <;> simp
    simp [hτ, hvv]

/-- The all-`false` labelling has `trueCount` zero. -/
theorem trueCount_const_false {V : Type*} [Fintype V] : trueCount (fun _ : V => false) = 0 := by
  rw [trueCount, Finset.card_eq_zero]
  ext v
  simp

/-- The indicator labelling of a single vertex has `trueCount` one. -/
theorem trueCount_single {V : Type*} [Fintype V] [DecidableEq V] (v₀ : V) :
    trueCount (fun v => decide (v = v₀)) = 1 := by
  rw [trueCount]
  have hset : (Finset.univ.filter fun v : V => decide (v = v₀) = true) = {v₀} := by
    ext v
    simp [decide_eq_true_eq]
  rw [hset, Finset.card_singleton]

/-! ### The bridge to the graphon homomorphism density -/

/-- The block measures of `A = [0,c]` give the weight `c^{k(τ)} (1-c)^{n-k(τ)}`. -/
theorem prod_blockMeasure_Icc {V : Type*} [Fintype V] {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (τ : V → Bool) :
    (∏ v, blockMeasure (Set.Icc 0 c) (τ v))
      = c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ) := by
  have hbm : ∀ b : Bool, blockMeasure (Set.Icc 0 c) b = if b = true then c else 1 - c := by
    intro b
    cases b
    · show (unitμ (Set.Icc 0 c)ᶜ).toReal = _
      rw [prob_compl_eq_one_sub measurableSet_Icc,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one,
        unitμ_Icc_toReal hc0 hc1]
      simp
    · show (unitμ (Set.Icc 0 c)).toReal = _
      rw [unitμ_Icc_toReal hc0 hc1]
      simp
  have hτc : trueCount τ = (Finset.univ.filter fun v => τ v = true).card := rfl
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (fun v => τ v = true)
  rw [Finset.card_univ] at hsum
  calc (∏ v, blockMeasure (Set.Icc 0 c) (τ v))
      = ∏ v, (if τ v = true then c else 1 - c) := Finset.prod_congr rfl fun v _ => hbm (τ v)
    _ = (∏ _v ∈ Finset.univ.filter fun v => τ v = true, c)
        * ∏ _v ∈ Finset.univ.filter fun v => ¬ τ v = true, (1 - c) := Finset.prod_ite _ _
    _ = c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ) := by
        rw [Finset.prod_const, Finset.prod_const, hτc]
        congr 2
        omega

/-- **`t(H, V_{c,a,s,q}) = tBip H a s q c`**: the homomorphism density of the concrete
two-block graphon with block `[0,c]` is the labelling polynomial. -/
theorem tBip_eq_tDensity {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {a s q c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hq : q ∈ Set.Icc (0:ℝ) 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (bipodalGraphon (Set.Icc 0 c) measurableSet_Icc a s q ha hs hq).tDensity H
      = tBip H a s q c := by
  rw [bipodalGraphon_tDensity_sum, tBip]
  exact Finset.sum_congr rfl fun τ _ => by
    rw [prod_blockMeasure_Icc hc0 hc1 τ]; rfl

/-! ### Continuity in `(q, c)` -/

/-- `tBip` is continuous in the pair `(q, c)` (for fixed `a`, `s`). -/
theorem continuous_tBip {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (a s : ℝ) :
    Continuous fun p : ℝ × ℝ => tBip H a s p.1 p.2 := by
  refine continuous_finsetSum _ fun τ _ => Continuous.mul ?_ ?_
  · -- the edge factor is continuous in `q`
    have hq : Continuous fun q : ℝ => edgeProd H a s q τ := by
      refine continuous_finsetProd _ fun e _ => ?_
      induction e using Sym2.ind with
      | _ x y =>
        show Continuous fun q : ℝ => blockVal a s q (τ x) (τ y)
        cases τ x <;> cases τ y <;>
          first
            | exact continuous_id
            | exact continuous_const
    exact hq.comp continuous_fst
  · -- the weight is continuous in `c`
    have hc : Continuous fun c : ℝ =>
        c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ) :=
      (continuous_pow _).mul ((continuous_const.sub continuous_id).pow _)
    exact hc.comp continuous_snd

/-! ### The small-block expansion -/

/-- **Small-block expansion of the bipodal `H`-density polynomial** for a `d`-regular `H`:
`tBip = (1-c)^n q^m + n c (1-c)^{n-1} s^d q^{m-d} + tBipRem`. -/
theorem tBip_expansion {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) (a s q c : ℝ) :
    tBip H a s q c
      = (1 - c) ^ (Fintype.card V) * q ^ H.edgeFinset.card
        + (Fintype.card V : ℝ) * c * (1 - c) ^ (Fintype.card V - 1)
          * (s ^ d * q ^ (H.edgeFinset.card - d))
        + tBipRem H a s q c := by
  classical
  -- the labellings with at most one marked vertex
  have hfilter_eq : Finset.univ.filter (fun τ : V → Bool => ¬ trueCount τ ≤ 1)
      = Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hrem : tBipRem H a s q c
      = ∑ τ ∈ Finset.univ.filter (fun τ : V → Bool => ¬ trueCount τ ≤ 1),
          edgeProd H a s q τ
            * (c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ)) := by
    rw [hfilter_eq]; rfl
  have hsplit : tBip H a s q c
      = (∑ τ ∈ Finset.univ.filter (fun τ : V → Bool => trueCount τ ≤ 1),
          edgeProd H a s q τ
            * (c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ)))
        + tBipRem H a s q c := by
    rw [hrem]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- identify the low-count labellings
  have hlow : (Finset.univ.filter (fun τ : V → Bool => trueCount τ ≤ 1))
      = insert (fun _ => false)
          ((Finset.univ : Finset V).image fun v₀ => (fun v => decide (v = v₀))) := by
    ext τ
    constructor
    · intro hτ
      have hk : trueCount τ ≤ 1 := (Finset.mem_filter.mp hτ).2
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h0 | h1
      · rw [label_eq_const_false h0]
        exact Finset.mem_insert_self _ _
      · obtain ⟨v₀, hτeq⟩ := label_eq_single h1
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨v₀, Finset.mem_univ v₀, hτeq.symm⟩)
    · intro hτ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ τ, ?_⟩
      rcases Finset.mem_insert.mp hτ with rfl | hmem
      · rw [trueCount_const_false]; omega
      · obtain ⟨v₀, _, rfl⟩ := Finset.mem_image.mp hmem
        rw [trueCount_single]
  have hnotmem : (fun _ : V => false)
      ∉ (Finset.univ : Finset V).image fun v₀ => (fun v => decide (v = v₀)) := by
    intro hmem
    obtain ⟨v₀, _, heq⟩ := Finset.mem_image.mp hmem
    have := congrFun heq v₀
    simp at this
  have hinj : ∀ x ∈ (Finset.univ : Finset V), ∀ y ∈ (Finset.univ : Finset V),
      (fun v => decide (v = x)) = (fun v => decide (v = y)) → x = y := by
    intro x _ y _ h
    have := congrFun h x
    simpa [decide_eq_decide] using this
  -- evaluate the two low-count contributions
  have hfalse : edgeProd H a s q (fun _ => false)
      * (c ^ trueCount (fun _ : V => false)
          * (1 - c) ^ (Fintype.card V - trueCount (fun _ : V => false)))
      = (1 - c) ^ (Fintype.card V) * q ^ H.edgeFinset.card := by
    rw [edgeProd_const_false, trueCount_const_false, pow_zero, one_mul, Nat.sub_zero]
    ring
  have hsingle : ∀ v₀ : V, edgeProd H a s q (fun v => decide (v = v₀))
      * (c ^ trueCount (fun v => decide (v = v₀))
          * (1 - c) ^ (Fintype.card V - trueCount (fun v => decide (v = v₀))))
      = c * (1 - c) ^ (Fintype.card V - 1) * (s ^ d * q ^ (H.edgeFinset.card - d)) := by
    intro v₀
    rw [edgeProd_single, trueCount_single, hreg v₀, pow_one]
    ring
  rw [hsplit, hlow, Finset.sum_insert hnotmem, Finset.sum_image hinj, hfalse,
    Finset.sum_congr rfl fun v₀ _ => hsingle v₀, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- The remainder is nonnegative (for parameters in `[0,1]`). -/
theorem tBipRem_nonneg {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {a s q c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hq : q ∈ Set.Icc (0:ℝ) 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ tBipRem H a s q c := by
  refine Finset.sum_nonneg fun τ _ => mul_nonneg (edgeProd_mem_Icc H ha hs hq τ).1 ?_
  have h1c : (0:ℝ) ≤ 1 - c := by linarith
  positivity

/-- The remainder is `O(c²)`: `tBipRem ≤ 2^n c²` (for parameters in `[0,1]`). -/
theorem tBipRem_le {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {a s q c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hq : q ∈ Set.Icc (0:ℝ) 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    tBipRem H a s q c ≤ 2 ^ (Fintype.card V) * c ^ 2 := by
  have h1c0 : (0:ℝ) ≤ 1 - c := by linarith
  have hterm : ∀ τ ∈ Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ),
      edgeProd H a s q τ * (c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ))
        ≤ c ^ 2 := by
    intro τ hτ
    have h2k : 2 ≤ trueCount τ := (Finset.mem_filter.mp hτ).2
    have hck : c ^ trueCount τ ≤ c ^ 2 := pow_le_pow_of_le_one hc0 hc1 h2k
    have h1ck : (1 - c) ^ (Fintype.card V - trueCount τ) ≤ 1 :=
      pow_le_one₀ h1c0 (by linarith)
    have hP := edgeProd_mem_Icc H ha hs hq τ
    calc edgeProd H a s q τ * (c ^ trueCount τ * (1 - c) ^ (Fintype.card V - trueCount τ))
        ≤ 1 * (c ^ 2 * 1) := by
          refine mul_le_mul hP.2 ?_ ?_ zero_le_one
          · exact mul_le_mul hck h1ck (by positivity) (by positivity)
          · positivity
      _ = c ^ 2 := by ring
  calc tBipRem H a s q c
      ≤ ∑ _τ ∈ Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ), c ^ 2 :=
        Finset.sum_le_sum hterm
    _ = ((Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ)).card : ℝ) * c ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (Fintype.card V) * c ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg c)
        have hcard : (Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ)).card
            ≤ 2 ^ (Fintype.card V) := by
          calc (Finset.univ.filter (fun τ : V → Bool => 2 ≤ trueCount τ)).card
              ≤ (Finset.univ : Finset (V → Bool)).card := Finset.card_filter_le _ _
            _ = 2 ^ (Fintype.card V) := by
                rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
        exact_mod_cast hcard

/-- Composed continuity: `c ↦ tBip H a s (φ c) c - b` is continuous along a continuous
path `φ` of large-block densities (the form consumed by the intermediate value theorem). -/
theorem continuousOn_tBip_comp_sub {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (a s b : ℝ) {φ : ℝ → ℝ} {S : Set ℝ}
    (hφ : ContinuousOn φ S) :
    ContinuousOn (fun c => tBip H a s (φ c) c - b) S := by
  have h := (continuous_tBip H a s).comp_continuousOn (hφ.prodMk continuousOn_id)
  exact h.sub continuousOn_const

-- The labelling sum over `V → Bool` must never be unfolded by `whnf`/`isDefEq` in
-- downstream files (it blows up the elaborator); all access goes through the API above.
attribute [irreducible] tBip tBipRem edgeProd

end UpperTailOptimizers
