import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.Stationarity

/-!
# The first variation of `t(H,·)` at a rank-one graphon

The second half of the reduction of `eq:graphon-stationarity`: for `H` `d`-regular on `v`
vertices, `W = f⊗f` and a bounded symmetric direction `U`,

  `d/dε|_{ε=0} t(H, W + εU) = m q(f)^{v-2} ∬ f(x)^{d-1} f(y)^{d-1} U(x,y) dx dy`,

the display the paper obtains by "differentiating one of the `m` edge factors".

Two ingredients:

* `prod_erase_edge` — dropping one edge from the product over `E(H)` leaves
  `f(x_a)^{d-1} f(x_b)^{d-1} ∏_{v ≠ a,b} f(x_v)^d`: the degree count
  `prod_edges_eq_prod_pow_degree` with one factor removed;
* `integral_pair_mul_rest` — that integral factors as `(∬ …)·q^{v-2}`, because the coordinate
  evaluations of `Measure.pi` are independent: the pair `(x_a, x_b)` is independent of the
  remaining `v-2` coordinates, and its law is `gμ` (`measurePreserving_pair`).

## Contents

* `edgeVal`, `rankOneKernel` — the edge value of a kernel at a labelling, and `f ⊗ f`;
* `prod_erase_edge`, `integral_pair_mul_rest` — the two ingredients;
* `hasDerivAt_tDensity_pert` — the first variation for a general graphon, as a sum over edges;
* `tDensity_variation_rankOne` — its rank-one `d`-regular evaluation.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Filter Topology Finset

/-! ## Edge values -/

/-- The value of a symmetric kernel on an edge `e` at a labelling `x`. -/
noncomputable def edgeVal {V : Type*} (w : SymKernel) (x : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun a b => w.toFun (x a) (x b), fun a b => w.symm' (x a) (x b)⟩ e

@[simp] theorem edgeVal_mk {V : Type*} (w : SymKernel) (x : V → ℝ) (a b : V) :
    edgeVal w x s(a, b) = w.toFun (x a) (x b) := rfl

theorem tDensity_eq_integral_edgeVal (w : SymKernel) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    w.tDensity H = ∫ x : V → ℝ, ∏ e ∈ H.edgeFinset, edgeVal w x e ∂(Measure.pi fun _ => unitμ) :=
  rfl

theorem edgeVal_pert {V : Type*} (w : SymKernel) (U : Direction) (ε : ℝ) (x : V → ℝ)
    (e : Sym2 V) : edgeVal (w.pert U ε) x e = edgeVal w x e + ε * edgeVal U.toSymKernel x e := by
  induction e using Sym2.ind with
  | _ a b => rfl

/-- The rank-one kernel `f ⊗ f`. -/
noncomputable def rankOneKernel {f : ℝ → ℝ} (hf : Measurable f) : SymKernel where
  toFun x y := f x * f y
  symm' _ _ := mul_comm _ _
  meas' := (hf.comp measurable_fst).mul (hf.comp measurable_snd)

@[simp] theorem rankOneKernel_toFun {f : ℝ → ℝ} (hf : Measurable f) (x y : ℝ) :
    (rankOneKernel hf).toFun x y = f x * f y := rfl

/-! ## Dropping one edge from the degree count -/

/-- **The edge product with one edge removed.**  For `d`-regular `H` and a positive `f`,

  `∏_{e ≠ s(a,b)} f(x_u)f(x_w) = f(x_a)^{d-1} f(x_b)^{d-1} ∏_{v ≠ a,b} f(x_v)^d`.

Both sides become `∏_v f(x_v)^d` after multiplying by the removed factor `f(x_a)f(x_b)`, which
is nonzero. -/
theorem prod_erase_edge {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {f : ℝ → ℝ} (hf : Measurable f)
    (hfpos : ∀ y, 0 < f y) {a b : V} (hab : H.Adj a b) (x : V → ℝ) :
    (∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal (rankOneKernel hf) x e)
      = f (x a) ^ (d - 1) * f (x b) ^ (d - 1)
        * ∏ v ∈ (Finset.univ.erase a).erase b, f (x v) ^ d := by
  classical
  have hne : a ≠ b := hab.ne
  have hmem : s(a, b) ∈ H.edgeFinset := by
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  have hd1 : 1 ≤ d := by
    have : 1 ≤ H.degree a := by
      rw [SimpleGraph.degree]
      exact Finset.card_pos.mpr ⟨b, by simpa using hab⟩
    rwa [hreg a] at this
  -- the full product is the degree product
  have hfull : (∏ e ∈ H.edgeFinset, edgeVal (rankOneKernel hf) x e) = ∏ v, f (x v) ^ d := by
    have := prod_edges_eq_prod_pow_degree H (fun v => f (x v))
    rw [show (∏ e ∈ H.edgeFinset, edgeVal (rankOneKernel hf) x e)
        = ∏ e ∈ H.edgeFinset, Sym2.lift
            ⟨fun u w => f (x u) * f (x w), fun _ _ => mul_comm _ _⟩ e from rfl, this]
    exact Finset.prod_congr rfl fun v _ => by rw [hreg v]
  -- split off the removed edge
  have hsplit : edgeVal (rankOneKernel hf) x s(a, b)
      * ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal (rankOneKernel hf) x e
      = ∏ e ∈ H.edgeFinset, edgeVal (rankOneKernel hf) x e :=
    Finset.mul_prod_erase _ _ hmem
  -- the right-hand side satisfies the same equation
  have hrhs : f (x a) * f (x b)
      * (f (x a) ^ (d - 1) * f (x b) ^ (d - 1)
        * ∏ v ∈ (Finset.univ.erase a).erase b, f (x v) ^ d) = ∏ v, f (x v) ^ d := by
    have hpa : f (x a) * f (x a) ^ (d - 1) = f (x a) ^ d := by
      rw [← pow_succ']; congr 1; omega
    have hpb : f (x b) * f (x b) ^ (d - 1) = f (x b) ^ d := by
      rw [← pow_succ']; congr 1; omega
    have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ b⟩
    have h1 : f (x b) ^ d * ∏ v ∈ (Finset.univ.erase a).erase b, f (x v) ^ d
        = ∏ v ∈ Finset.univ.erase a, f (x v) ^ d :=
      Finset.mul_prod_erase _ (fun v => f (x v) ^ d) hb
    have h2 : f (x a) ^ d * ∏ v ∈ Finset.univ.erase a, f (x v) ^ d = ∏ v, f (x v) ^ d :=
      Finset.mul_prod_erase _ (fun v => f (x v) ^ d) (Finset.mem_univ a)
    calc f (x a) * f (x b)
          * (f (x a) ^ (d - 1) * f (x b) ^ (d - 1)
            * ∏ v ∈ (Finset.univ.erase a).erase b, f (x v) ^ d)
        = (f (x a) * f (x a) ^ (d - 1))
          * ((f (x b) * f (x b) ^ (d - 1))
            * ∏ v ∈ (Finset.univ.erase a).erase b, f (x v) ^ d) := by ring
      _ = f (x a) ^ d * (f (x b) ^ d * ∏ v ∈ (Finset.univ.erase a).erase b, f (x v) ^ d) := by
          rw [hpa, hpb]
      _ = ∏ v, f (x v) ^ d := by rw [h1, h2]
  have hnz : f (x a) * f (x b) ≠ 0 := ne_of_gt (mul_pos (hfpos _) (hfpos _))
  refine mul_left_cancel₀ hnz ?_
  rw [hrhs]
  rw [show f (x a) * f (x b) = edgeVal (rankOneKernel hf) x s(a, b) from rfl, hsplit, hfull]


/-! ## Factoring the pair off the remaining coordinates -/

/-- **The pair/rest factorisation.**  The coordinate evaluations of `Measure.pi` are independent,
so a function of `(x_a, x_b)` is independent of a product over the other coordinates:

  `∫ Φ(x_a,x_b) ∏_{v ≠ a,b} k(x_v) = (∬ Φ) · (∫ k)^{v-2}`.

The pair marginal is `gμ` (`measurePreserving_pair`), and the remaining product factors
coordinate by coordinate (`integral_fintype_prod_eq_prod`). -/
theorem integral_pair_mul_rest {V : Type*} [Fintype V] [DecidableEq V] {a b : V} (hab : a ≠ b)
    {Φ : ℝ → ℝ → ℝ} (hΦ : Measurable fun z : ℝ × ℝ => Φ z.1 z.2)
    {k : ℝ → ℝ} (hk : Measurable k) :
    ∫ x : V → ℝ, Φ (x a) (x b) * ∏ v ∈ (Finset.univ.erase a).erase b, k (x v)
        ∂(Measure.pi fun _ : V => unitμ)
      = (∫ z, Φ z.1 z.2 ∂gμ) * (∫ y, k y ∂unitμ) ^ (Fintype.card V - 2) := by
  classical
  set s : Finset V := (Finset.univ.erase a).erase b with hsdef
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  -- the two factors are independent
  have hindep : ProbabilityTheory.iIndepFun (fun (i : V) (ω : V → ℝ) => ω i) π :=
    ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
  have hdisj : Disjoint ({a, b} : Finset V) s := by
    refine Finset.disjoint_left.mpr fun i hi hi' => ?_
    rw [hsdef, Finset.mem_erase, Finset.mem_erase] at hi'
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hi'.2.1 rfl
    · exact hi'.1 (Finset.mem_singleton.mp hi)
  have hST := hindep.indepFun_finset ({a, b} : Finset V) s hdisj (fun i => measurable_pi_apply i)
  have hameme : a ∈ ({a, b} : Finset V) := Finset.mem_insert_self a _
  have hbmeme : b ∈ ({a, b} : Finset V) := Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hg1 : Measurable fun y : (({a, b} : Finset V)) → ℝ =>
      Φ (y ⟨a, hameme⟩) (y ⟨b, hbmeme⟩) := by
    have hpair : Measurable fun y : (({a, b} : Finset V)) → ℝ =>
        (y ⟨a, hameme⟩, y ⟨b, hbmeme⟩) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    simpa [Function.comp_def] using hΦ.comp hpair
  have hg2 : Measurable fun y : ↥s → ℝ => ∏ i : ↥s, k (y i) :=
    Finset.measurable_prod _ fun i _ => hk.comp (measurable_pi_apply i)
  have hindep2 := hST.comp hg1 hg2
  have heq1 : (fun y : (({a, b} : Finset V)) → ℝ => Φ (y ⟨a, hameme⟩) (y ⟨b, hbmeme⟩))
      ∘ (fun (ω : V → ℝ) (i : (({a, b} : Finset V))) => ω i)
      = fun ω : V → ℝ => Φ (ω a) (ω b) := rfl
  have heq2 : (fun y : ↥s → ℝ => ∏ i : ↥s, k (y i))
      ∘ (fun (ω : V → ℝ) (i : (s : Finset V)) => ω i)
      = fun ω : V → ℝ => ∏ v ∈ s, k (ω v) := by
    funext ω
    exact Finset.prod_coe_sort s fun v => k (ω v)
  rw [heq1, heq2] at hindep2
  -- measurability of the two factors on `V → ℝ`
  have hm1 : Measurable fun ω : V → ℝ => Φ (ω a) (ω b) := by
    have hpair : Measurable fun ω : V → ℝ => (ω a, ω b) :=
      (measurable_pi_apply a).prodMk (measurable_pi_apply b)
    simpa [Function.comp_def] using hΦ.comp hpair
  have hm2 : Measurable fun ω : V → ℝ => ∏ v ∈ s, k (ω v) :=
    Finset.measurable_prod _ fun v _ => hk.comp (measurable_pi_apply v)
  have hsplit := hindep2.integral_mul_eq_mul_integral hm1.aestronglyMeasurable
    hm2.aestronglyMeasurable
  simp only [Pi.mul_apply] at hsplit
  -- the pair integral is against `gμ`
  have hpair : ∫ ω : V → ℝ, Φ (ω a) (ω b) ∂π = ∫ z, Φ z.1 z.2 ∂gμ := by
    have hmap := (measurePreserving_pair (V := V) hab).map_eq
    have hmeasφ : Measurable fun x : V → ℝ => (x a, x b) :=
      (measurable_pi_apply a).prodMk (measurable_pi_apply b)
    rw [show gμ = unitμ.prod unitμ from rfl, ← hmap,
      integral_map hmeasφ.aemeasurable hΦ.aestronglyMeasurable]
  -- the remaining coordinates factor
  have hrest : ∫ ω : V → ℝ, (∏ v ∈ s, k (ω v)) ∂π
      = (∫ y, k y ∂unitμ) ^ (Fintype.card V - 2) := by
    set F : V → ℝ → ℝ := fun v y => if v ∈ s then k y else 1 with hFdef
    have hprod : ∀ ω : V → ℝ, (∏ v, F v (ω v)) = ∏ v ∈ s, k (ω v) := by
      intro ω
      simp [hFdef]
    have hcard : s.card = Fintype.card V - 2 := by
      have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
      rw [hsdef, Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ]
      omega
    have hval : ∀ v : V, (∫ y, F v y ∂unitμ) = if v ∈ s then ∫ y, k y ∂unitμ else 1 := by
      intro v
      by_cases hv : v ∈ s <;> simp [hFdef, hv]
    calc ∫ ω : V → ℝ, (∏ v ∈ s, k (ω v)) ∂π
        = ∫ ω : V → ℝ, (∏ v, F v (ω v)) ∂π := by
          simp only [hprod]
      _ = ∏ v, ∫ y, F v y ∂unitμ := integral_fintype_prod_eq_prod F
      _ = ∏ v, (if v ∈ s then ∫ y, k y ∂unitμ else 1) := Finset.prod_congr rfl fun v _ => hval v
      _ = ∏ _v ∈ s, ∫ y, k y ∂unitμ := by simp
      _ = (∫ y, k y ∂unitμ) ^ (Fintype.card V - 2) := by rw [Finset.prod_const, hcard]
  rw [hsplit, hpair, hrest]


/-! ## The first variation of `t(H,·)` -/

/-- The edge value is measurable in the labelling. -/
theorem measurable_edgeVal {V : Type*} [Fintype V] [DecidableEq V] (w : SymKernel) (e : Sym2 V) :
    Measurable fun x : V → ℝ => edgeVal w x e := by
  induction e using Sym2.ind with
  | _ a b =>
    have hpair : Measurable fun x : V → ℝ => (x a, x b) :=
      (measurable_pi_apply a).prodMk (measurable_pi_apply b)
    simpa [Function.comp_def] using w.meas'.comp hpair

/-- **The first variation of `t(H,·)`.**  Differentiating the product over `E(H)` one factor at a
time (`HasDerivAt.fun_finsetProd`) under the integral sign:

  `d/dε|_{ε=0} t(H, W+εU) = ∫ ∑_{e ∈ E(H)} U(x_e) ∏_{e' ≠ e} W(x_{e'})`.

The domination is trivial: on the window where `W + εU` stays in `[0,1]` each factor is at most
`1` in absolute value, so the derivative is bounded by `e(H)·(|U.bound|+1)`. -/
theorem hasDerivAt_tDensity_pert {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (W : Graphon) (U : Direction) {η : ℝ} (hη : 0 < η)
    (hW0 : ∀ x y, η ≤ W.toFun x y) (hW1 : ∀ x y, W.toFun x y ≤ 1 - η) :
    HasDerivAt (fun ε : ℝ => ((graphonKernel W).pert U ε).tDensity H)
      (∫ x : V → ℝ, ∑ e ∈ H.edgeFinset,
        (∏ e' ∈ H.edgeFinset.erase e, edgeVal (graphonKernel W) x e')
          * edgeVal U.toSymKernel x e ∂(Measure.pi fun _ : V => unitμ)) 0 := by
  classical
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  set δ : ℝ := η / (2 * (|U.bound| + 1)) with hδdef
  have hb0 : (0 : ℝ) < |U.bound| + 1 := by positivity
  have hδ : 0 < δ := by rw [hδdef]; positivity
  set F : ℝ → (V → ℝ) → ℝ :=
    fun ε x => ∏ e ∈ H.edgeFinset, edgeVal ((graphonKernel W).pert U ε) x e with hF
  set F' : ℝ → (V → ℝ) → ℝ :=
    fun ε x => ∑ e ∈ H.edgeFinset,
      (∏ e' ∈ H.edgeFinset.erase e, edgeVal ((graphonKernel W).pert U ε) x e')
        * edgeVal U.toSymKernel x e with hF'
  set S : Set ℝ := Metric.ball (0 : ℝ) δ with hS
  have hSmem : S ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hδ
  -- on the window every edge value stays in `[0,1]`
  have hval : ∀ ε ∈ S, ∀ (x : V → ℝ) (e : Sym2 V),
      edgeVal ((graphonKernel W).pert U ε) x e ∈ Set.Icc (0 : ℝ) 1 := by
    intro ε hε x e
    have hεabs : |ε| < δ := by simpa [hS, Real.dist_eq] using hε
    induction e using Sym2.ind with
    | _ a b =>
      have hmem := pert_mem_Icc hη hW0 hW1 hεabs (x a) (x b)
      have heq : edgeVal ((graphonKernel W).pert U ε) x s(a, b)
          = W.toFun (x a) (x b) + ε * U.toFun (x a) (x b) := rfl
      rw [heq]
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hUb : ∀ (x : V → ℝ) (e : Sym2 V), |edgeVal U.toSymKernel x e| ≤ |U.bound| + 1 := by
    intro x e
    induction e using Sym2.ind with
    | _ a b =>
      exact le_trans (le_trans (U.bound_ge (x a) (x b)) (le_abs_self _)) (by linarith)
  -- measurability
  have hmF : ∀ ε : ℝ, Measurable (F ε) := fun ε =>
    Finset.measurable_prod _ fun e _ => measurable_edgeVal _ e
  have hmF' : ∀ ε : ℝ, Measurable (F' ε) := fun ε =>
    Finset.measurable_sum _ fun e _ =>
      (Finset.measurable_prod _ fun e' _ => measurable_edgeVal _ e').mul (measurable_edgeVal _ e)
  -- the constant bound
  set C : ℝ := (H.edgeFinset.card : ℝ) * (|U.bound| + 1) with hC
  have hbound : ∀ ε ∈ S, ∀ x : V → ℝ, ‖F' ε x‖ ≤ C := by
    intro ε hε x
    rw [Real.norm_eq_abs, hF']
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ e ∈ H.edgeFinset,
        |(∏ e' ∈ H.edgeFinset.erase e, edgeVal ((graphonKernel W).pert U ε) x e')
          * edgeVal U.toSymKernel x e| ≤ |U.bound| + 1 := by
      intro e _
      rw [abs_mul]
      have hp : |∏ e' ∈ H.edgeFinset.erase e, edgeVal ((graphonKernel W).pert U ε) x e'| ≤ 1 := by
        rw [Finset.abs_prod]
        refine le_trans (Finset.prod_le_one (fun e' _ => abs_nonneg _) (fun e' _ => ?_)) le_rfl
        have := hval ε hε x e'
        rw [abs_of_nonneg this.1]; exact this.2
      calc |∏ e' ∈ H.edgeFinset.erase e, edgeVal ((graphonKernel W).pert U ε) x e'|
            * |edgeVal U.toSymKernel x e|
          ≤ 1 * (|U.bound| + 1) :=
            mul_le_mul hp (hUb x e) (abs_nonneg _) zero_le_one
        _ = |U.bound| + 1 := one_mul _
    calc ∑ e ∈ H.edgeFinset,
          |(∏ e' ∈ H.edgeFinset.erase e, edgeVal ((graphonKernel W).pert U ε) x e')
            * edgeVal U.toSymKernel x e|
        ≤ ∑ _e ∈ H.edgeFinset, (|U.bound| + 1) := Finset.sum_le_sum hterm
      _ = C := by rw [Finset.sum_const, hC, nsmul_eq_mul]
  -- integrability of the base integrand
  have hFint : Integrable (F 0) π := by
    refine integrable_of_abs_le (hmF 0) 1 (fun x => ?_)
    rw [hF, Finset.abs_prod]
    refine Finset.prod_le_one (fun e _ => abs_nonneg _) (fun e _ => ?_)
    have := hval 0 (Metric.mem_ball_self hδ) x e
    rw [abs_of_nonneg this.1]; exact this.2
  -- the pointwise derivative
  have hdiff : ∀ x : V → ℝ, ∀ ε ∈ S, HasDerivAt (fun ε : ℝ => F ε x) (F' ε x) ε := by
    intro x ε _
    have hstep : ∀ e ∈ H.edgeFinset,
        HasDerivAt (fun ε : ℝ => edgeVal ((graphonKernel W).pert U ε) x e)
          (edgeVal U.toSymKernel x e) ε := by
      intro e _
      have h : (fun ε : ℝ => edgeVal ((graphonKernel W).pert U ε) x e)
          = fun ε : ℝ => edgeVal (graphonKernel W) x e + ε * edgeVal U.toSymKernel x e :=
        funext fun ε => edgeVal_pert _ _ _ _ _
      rw [h]
      simpa using ((hasDerivAt_id ε).mul_const (edgeVal U.toSymKernel x e)).const_add
        (edgeVal (graphonKernel W) x e)
    have := HasDerivAt.fun_finsetProd (u := H.edgeFinset)
      (f := fun e ε => edgeVal ((graphonKernel W).pert U ε) x e)
      (f' := fun e => edgeVal U.toSymKernel x e) hstep
    simpa [hF, hF', smul_eq_mul, mul_comm] using this
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (bound := fun _ => C) (μ := π) hSmem
    (Eventually.of_forall fun ε => (hmF ε).aestronglyMeasurable) hFint
    (hmF' 0).aestronglyMeasurable
    (Eventually.of_forall fun x => fun ε hε => hbound ε hε x)
    (integrable_const C)
    (Eventually.of_forall fun x => hdiff x)
  have hzero : F' 0 = fun x : V → ℝ => ∑ e ∈ H.edgeFinset,
      (∏ e' ∈ H.edgeFinset.erase e, edgeVal (graphonKernel W) x e')
        * edgeVal U.toSymKernel x e := by
    funext x
    rw [hF']
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun e' _ => ?_
    rw [edgeVal_pert]; ring
  rw [← hzero]
  exact hkey.2


/-! ## The rank-one, `d`-regular evaluation -/

/-- **The paper's display for `d/dε t(H, W_ε)`.**  For `d`-regular `H` and `W = f⊗f`, each of the
`e(H)` edge terms contributes the same amount, and

  `d/dε|_{ε=0} t(H, f⊗f + εU) = m q(f)^{v-2} ∬ f(x)^{d-1} f(y)^{d-1} U(x,y)`,

with `q(f) = ∫ f^d`.  `prod_erase_edge` identifies the term of one edge and
`integral_pair_mul_rest` integrates it. -/
theorem tDensity_variation_rankOne {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hreg : ∀ v, H.degree v = d) {f : ℝ → ℝ} (hf : Measurable f)
    (hfpos : ∀ y, 0 < f y) (hfle : ∀ y, f y ≤ 1) (U : Direction) :
    ∫ x : V → ℝ, ∑ e ∈ H.edgeFinset,
        (∏ e' ∈ H.edgeFinset.erase e, edgeVal (rankOneKernel hf) x e')
          * edgeVal U.toSymKernel x e ∂(Measure.pi fun _ : V => unitμ)
      = (H.edgeFinset.card : ℝ) * (∫ y, f y ^ d ∂unitμ) ^ (Fintype.card V - 2)
        * ∫ z, f z.1 ^ (d - 1) * f z.2 ^ (d - 1) * U.toFun z.1 z.2 ∂gμ := by
  classical
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  set Φ : ℝ → ℝ → ℝ := fun y z => f y ^ (d - 1) * f z ^ (d - 1) * U.toFun y z with hΦdef
  have hΦm : Measurable fun z : ℝ × ℝ => Φ z.1 z.2 :=
    (((hf.comp measurable_fst).pow_const _).mul ((hf.comp measurable_snd).pow_const _)).mul U.meas'
  have hkm : Measurable fun y : ℝ => f y ^ d := hf.pow_const d
  -- each edge term is bounded, hence integrable
  have hterm_int : ∀ e ∈ H.edgeFinset, Integrable
      (fun x : V → ℝ => (∏ e' ∈ H.edgeFinset.erase e, edgeVal (rankOneKernel hf) x e')
        * edgeVal U.toSymKernel x e) π := by
    intro e _
    refine integrable_of_abs_le
      ((Finset.measurable_prod _ fun e' _ => measurable_edgeVal _ e').mul (measurable_edgeVal _ e))
      (|U.bound| + 1) (fun x => ?_)
    have hp : |∏ e' ∈ H.edgeFinset.erase e, edgeVal (rankOneKernel hf) x e'| ≤ 1 := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_one (fun e' _ => abs_nonneg _) (fun e' _ => ?_)
      induction e' using Sym2.ind with
      | _ u w =>
        have h0 : (0 : ℝ) ≤ f (x u) * f (x w) := le_of_lt (mul_pos (hfpos _) (hfpos _))
        have h1 : f (x u) * f (x w) ≤ 1 :=
          mul_le_one₀ (hfle _) (le_of_lt (hfpos _)) (hfle _)
        have heq : edgeVal (rankOneKernel hf) x s(u, w) = f (x u) * f (x w) := rfl
        rw [heq, abs_of_nonneg h0]; exact h1
    have hU : |edgeVal U.toSymKernel x e| ≤ |U.bound| + 1 := by
      induction e using Sym2.ind with
      | _ u w => exact le_trans (le_trans (U.bound_ge (x u) (x w)) (le_abs_self _)) (by linarith)
    rw [abs_mul]
    calc |∏ e' ∈ H.edgeFinset.erase e, edgeVal (rankOneKernel hf) x e'|
          * |edgeVal U.toSymKernel x e|
        ≤ 1 * (|U.bound| + 1) := mul_le_mul hp hU (abs_nonneg _) zero_le_one
      _ = |U.bound| + 1 := one_mul _
  rw [integral_finsetSum _ hterm_int]
  -- every edge contributes the same
  have hconst : ∀ e ∈ H.edgeFinset,
      ∫ x : V → ℝ, (∏ e' ∈ H.edgeFinset.erase e, edgeVal (rankOneKernel hf) x e')
          * edgeVal U.toSymKernel x e ∂π
        = (∫ z, Φ z.1 z.2 ∂gμ) * (∫ y, f y ^ d ∂unitμ) ^ (Fintype.card V - 2) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hadj : H.Adj a b := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hrw : ∀ x : V → ℝ,
          (∏ e' ∈ H.edgeFinset.erase s(a, b), edgeVal (rankOneKernel hf) x e')
            * edgeVal U.toSymKernel x s(a, b)
          = Φ (x a) (x b) * ∏ v ∈ (Finset.univ.erase a).erase b, f (x v) ^ d := by
        intro x
        rw [prod_erase_edge H hreg hf hfpos hadj x, hΦdef]
        have heq : edgeVal U.toSymKernel x s(a, b) = U.toFun (x a) (x b) := rfl
        rw [heq]; ring
      simp only [hrw]
      exact integral_pair_mul_rest hadj.ne hΦm hkm
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hΦdef]
  ring

end SingularEndpoint

end UpperTailOptimizers
