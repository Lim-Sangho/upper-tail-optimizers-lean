import UpperTailOptimizers.Preliminaries.KRRSBipodality.KernelBounds

/-!
# The terms of the edge expansion around a constant

For a bounded symmetric kernel `E` (in the application `E = W - ε`), expanding
`∏_{e ∈ E(H)} (ε + E_e)` produces the terms `∫ ∏_{e ∈ T} E_e` over edge sets `T ⊆ E(H)`.
This file evaluates or bounds each of them:

* `integral_star` — a star `T` centred at `u` integrates to `∫ δ(t)^{|T|} dt`, where
  `δ(t) = ∫ E(t,s) ds` is the row integral;
* `integral_isolated_edge` — a term with an isolated edge vanishes when `∬ E = 0`;
* `cherry_edge_bound` — two edges at a vertex together with a disjoint edge give `‖E‖₂³`;
* `exists_star_structure` — the combinatorial trichotomy behind the star reduction.
-/

namespace UpperTailOptimizers

open MeasureTheory SingularEndpoint

/-- A function of one coordinate integrates like the function itself. -/
theorem integral_pi_eval_comp {V : Type*} [Fintype V] [DecidableEq V] (u : V) {G : ℝ → ℝ}
    (hG : Measurable G) :
    ∫ y : V → ℝ, G (y u) ∂(Measure.pi fun _ : V => unitμ) = ∫ t, G t ∂unitμ := by
  have hmp := measurePreserving_eval (μ := fun _ : V => unitμ) u
  calc ∫ y : V → ℝ, G (y u) ∂(Measure.pi fun _ : V => unitμ)
      = ∫ t, G t ∂(Measure.map (fun y : V → ℝ => y u) (Measure.pi fun _ : V => unitμ)) :=
        (integral_map hmp.measurable.aemeasurable
          (by rw [hmp.map_eq]; exact hG.aestronglyMeasurable)).symm
    _ = ∫ t, G t ∂unitμ := by rw [show (fun y : V → ℝ => y u) = Function.eval u from rfl,
        hmp.map_eq]

namespace BKernel

variable (P : BKernel)

/-- The kernel value attached to an edge of a labelled vertex set. -/
def kEdge {V : Type*} (y : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun p q => P.E (y p) (y q), fun p q => P.symm' (y p) (y q)⟩ e

theorem kEdge_mk {V : Type*} (y : V → ℝ) (p q : V) : P.kEdge y s(p, q) = P.E (y p) (y q) :=
  rfl

theorem abs_kEdge_le {V : Type*} (y : V → ℝ) (e : Sym2 V) : |P.kEdge y e| ≤ 5 := by
  induction e using Sym2.ind with
  | _ p q => exact P.bound (y p) (y q)

theorem measurable_kEdge {V : Type*} (e : Sym2 V) : Measurable fun y : V → ℝ => P.kEdge y e := by
  induction e using Sym2.ind with
  | _ p q => exact P.measurable_residAt p q

theorem measurable_prod_kEdge {V : Type*} (T : Finset (Sym2 V)) :
    Measurable fun y : V → ℝ => ∏ e ∈ T, P.kEdge y e :=
  Finset.measurable_prod _ fun e _ => P.measurable_kEdge e

theorem abs_prod_kEdge_le {V : Type*} (T : Finset (Sym2 V)) (y : V → ℝ) :
    |∏ e ∈ T, P.kEdge y e| ≤ 5 ^ T.card := by
  rw [Finset.abs_prod]
  calc ∏ e ∈ T, |P.kEdge y e| ≤ ∏ _e ∈ T, (5:ℝ) :=
        Finset.prod_le_prod (fun e _ => abs_nonneg _) fun e _ => P.abs_kEdge_le y e
    _ = 5 ^ T.card := Finset.prod_const _

/-- The row integral `δ(t) = ∫ E(t,s) ds`. -/
noncomputable def rowInt (t : ℝ) : ℝ := ∫ s, P.E t s ∂unitμ

theorem measurable_rowInt : Measurable P.rowInt :=
  (P.meas.stronglyMeasurable).integral_prod_right'.measurable

theorem abs_rowInt_le (t : ℝ) : |P.rowInt t| ≤ 5 := by
  have h : ‖∫ s, P.E t s ∂unitμ‖ ≤ 5 * unitμ.real Set.univ :=
    norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using P.bound t s)
  have huniv : (5:ℝ) * unitμ.real Set.univ = 5 := by simp [measureReal_def]
  rw [huniv] at h
  show |∫ s, P.E t s ∂unitμ| ≤ 5
  simpa [Real.norm_eq_abs] using h

/-- `∫ δ = ∬ E`. -/
theorem integral_rowInt : ∫ t, P.rowInt t ∂unitμ = ∫ z, P.E z.1 z.2 ∂gμ := by
  have hint : Integrable (fun z : ℝ × ℝ => P.E z.1 z.2) gμ :=
    integrable_of_abs_le P.meas 5 fun z => P.bound z.1 z.2
  exact integral_integral hint

/-- **The star integral.**  If every edge of `T` joins `u` to another vertex, then integrating
out the leaves gives `∫ G(x_u) ∏_{e ∈ T} E_e = ∫ G(t) δ(t)^{|T|} dt`. -/
theorem integral_star {V : Type*} [Fintype V] [DecidableEq V] (u : V) (T : Finset (Sym2 V))
    (hT : ∀ e ∈ T, ∃ w, w ≠ u ∧ e = s(u, w)) {G : ℝ → ℝ} (hG : Measurable G) {CG : ℝ}
    (hGb : ∀ t, |G t| ≤ CG) :
    ∫ y : V → ℝ, G (y u) * ∏ e ∈ T, P.kEdge y e ∂(Measure.pi fun _ : V => unitμ)
      = ∫ t, G t * P.rowInt t ^ T.card ∂unitμ := by
  induction T using Finset.induction_on generalizing G CG with
  | empty =>
    simp only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero]
    exact integral_pi_eval_comp u hG
  | insert e T he ih =>
    obtain ⟨w, hwu, rfl⟩ := hT e (Finset.mem_insert_self _ _)
    have hT' : ∀ e ∈ T, ∃ w, w ≠ u ∧ e = s(u, w) := fun e' he' =>
      hT e' (Finset.mem_insert_of_mem he')
    have hupd : ∀ e' ∈ T, ∀ (y : V → ℝ) (s : ℝ),
        P.kEdge (Function.update y w s) e' = P.kEdge y e' := by
      intro e' he' y s
      obtain ⟨w', -, rfl⟩ := hT' e' he'
      have hw'w : w' ≠ w := by
        rintro rfl
        exact he he'
      show P.E (Function.update y w s u) (Function.update y w s w') = P.E (y u) (y w')
      rw [Function.update_of_ne (Ne.symm hwu), Function.update_of_ne hw'w]
    have hCG : 0 ≤ CG := le_trans (abs_nonneg _) (hGb 0)
    simp only [Finset.prod_insert he, Finset.card_insert_of_notMem he]
    have hmeasF : Measurable fun y : V → ℝ =>
        G (y u) * (P.kEdge y s(u, w) * ∏ e ∈ T, P.kEdge y e) :=
      (hG.comp (measurable_pi_apply u)).mul ((P.measurable_kEdge _).mul (P.measurable_prod_kEdge T))
    have hbF : ∀ y : V → ℝ,
        |G (y u) * (P.kEdge y s(u, w) * ∏ e ∈ T, P.kEdge y e)| ≤ CG * (5 * 5 ^ T.card) := by
      intro y
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hGb _) (mul_le_mul (P.abs_kEdge_le y _) (P.abs_prod_kEdge_le T y)
        (abs_nonneg _) (by norm_num)) (by positivity) hCG
    rw [integral_pi_update w hmeasF hbF]
    have hinner : ∀ y : V → ℝ,
        ∫ s, G (Function.update y w s u) * (P.kEdge (Function.update y w s) s(u, w)
          * ∏ e ∈ T, P.kEdge (Function.update y w s) e) ∂unitμ
        = (G (y u) * P.rowInt (y u)) * ∏ e ∈ T, P.kEdge y e := by
      intro y
      have hpt : ∀ s : ℝ, G (Function.update y w s u) * (P.kEdge (Function.update y w s) s(u, w)
          * ∏ e ∈ T, P.kEdge (Function.update y w s) e)
          = (G (y u) * ∏ e ∈ T, P.kEdge y e) * P.E (y u) s := by
        intro s
        rw [Finset.prod_congr rfl fun e' he' => hupd e' he' y s, kEdge_mk,
          Function.update_of_ne (Ne.symm hwu), Function.update_self]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
      unfold rowInt
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
    have hG' : ∀ t, |G t * P.rowInt t| ≤ CG * 5 := fun t => by
      rw [abs_mul]
      exact mul_le_mul (hGb t) (P.abs_rowInt_le t) (abs_nonneg _) hCG
    have hih := ih (G := fun t => G t * P.rowInt t) hT' (hG.mul P.measurable_rowInt) hG'
    refine hih.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_))
    show G t * P.rowInt t * P.rowInt t ^ T.card = G t * P.rowInt t ^ (T.card + 1)
    ring

/-- Re-randomising a vertex off an edge does not change the edge value. -/
theorem kEdge_update_of_notMem {V : Type*} [DecidableEq V] (y : V → ℝ) {w : V} (s : ℝ)
    {e : Sym2 V} (hw : w ∉ e) : P.kEdge (Function.update y w s) e = P.kEdge y e := by
  revert hw
  induction e using Sym2.ind with
  | _ p q =>
    intro hw
    rw [Sym2.mem_iff] at hw
    push Not at hw
    show P.E (Function.update y w s p) (Function.update y w s q) = P.E (y p) (y q)
    rw [Function.update_of_ne (Ne.symm hw.1), Function.update_of_ne (Ne.symm hw.2)]

/-- **A term with an isolated edge vanishes** when `∬ E = 0`: integrating out the two
endpoints of the isolated edge `s(a,b)` produces the factor `∬ E`. -/
theorem integral_isolated_edge {V : Type*} [Fintype V] [DecidableEq V] (T : Finset (Sym2 V))
    {a b : V} (hab : a ≠ b) (hmem : s(a, b) ∈ T)
    (hiso : ∀ e ∈ T, e ≠ s(a, b) → a ∉ e ∧ b ∉ e)
    (hzero : ∫ z, P.E z.1 z.2 ∂gμ = 0) :
    ∫ y : V → ℝ, ∏ e ∈ T, P.kEdge y e ∂(Measure.pi fun _ : V => unitμ) = 0 := by
  set R : (V → ℝ) → ℝ := fun y => ∏ e ∈ T.erase s(a, b), P.kEdge y e with hR
  have hRmeas : Measurable R := P.measurable_prod_kEdge _
  have hRb : ∀ y, |R y| ≤ 5 ^ (T.erase s(a, b)).card := fun y => P.abs_prod_kEdge_le _ y
  have hRupd : ∀ (y : V → ℝ) (s : ℝ) (w : V), (w = a ∨ w = b) →
      R (Function.update y w s) = R y := by
    intro y s w hw
    refine Finset.prod_congr rfl fun e he => P.kEdge_update_of_notMem y s ?_
    have h := hiso e (Finset.mem_of_mem_erase he) (Finset.ne_of_mem_erase he)
    rcases hw with rfl | rfl
    · exact h.1
    · exact h.2
  have hsplit : ∀ y : V → ℝ, ∏ e ∈ T, P.kEdge y e = R y * P.E (y a) (y b) := by
    intro y
    rw [← Finset.mul_prod_erase T _ hmem, kEdge_mk]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  have h5 : (0:ℝ) ≤ 5 ^ (T.erase s(a, b)).card := by positivity
  -- integrate out `b`
  have hF1 : Measurable fun y : V → ℝ => R y * P.E (y a) (y b) :=
    hRmeas.mul (P.measurable_residAt a b)
  have hbF1 : ∀ y : V → ℝ, |R y * P.E (y a) (y b)| ≤ 5 ^ (T.erase s(a, b)).card * 5 :=
    fun y => by
      rw [abs_mul]; exact mul_le_mul (hRb y) (P.bound _ _) (abs_nonneg _) h5
  rw [integral_pi_update b hF1 hbF1]
  have hin1 : ∀ y : V → ℝ, ∫ s, R (Function.update y b s)
      * P.E (Function.update y b s a) (Function.update y b s b) ∂unitμ
      = R y * P.rowInt (y a) := by
    intro y
    have hpt : ∀ s : ℝ, R (Function.update y b s)
        * P.E (Function.update y b s a) (Function.update y b s b) = R y * P.E (y a) s := by
      intro s
      rw [hRupd y s b (Or.inr rfl), Function.update_of_ne hab, Function.update_self]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hin1)]
  -- integrate out `a`
  have hF2 : Measurable fun y : V → ℝ => R y * P.rowInt (y a) :=
    hRmeas.mul (P.measurable_rowInt.comp (measurable_pi_apply a))
  have hbF2 : ∀ y : V → ℝ, |R y * P.rowInt (y a)| ≤ 5 ^ (T.erase s(a, b)).card * 5 :=
    fun y => by
      rw [abs_mul]; exact mul_le_mul (hRb y) (P.abs_rowInt_le _) (abs_nonneg _) h5
  rw [integral_pi_update a hF2 hbF2]
  have hin2 : ∀ y : V → ℝ, ∫ s, R (Function.update y a s)
      * P.rowInt (Function.update y a s a) ∂unitμ = 0 := by
    intro y
    have hpt : ∀ s : ℝ, R (Function.update y a s) * P.rowInt (Function.update y a s a)
        = R y * P.rowInt s := by
      intro s
      rw [hRupd y s a (Or.inl rfl), Function.update_self]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      P.integral_rowInt, hzero, mul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hin2)]
  simp

/-- `∫ g ≤ ‖E‖₂` for the row norm `g`. -/
theorem integral_rowNorm_le : ∫ t, P.rowNorm t ∂unitμ ≤ P.residL2 := by
  have hint : Integrable P.rowNorm unitμ :=
    integrable_of_abs_le P.measurable_rowNorm 5 fun t => by
      rw [abs_of_nonneg (P.rowNorm_nonneg t)]; exact P.rowNorm_le t
  have hint2 : Integrable (fun t => P.rowNorm t ^ 2) unitμ :=
    integrable_of_abs_le (P.measurable_rowNorm.pow_const 2) 25 fun t => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [P.rowNorm_le t, P.rowNorm_nonneg t]
  have h := integral_abs_le_sqrt hint hint2
  have habs : ∫ t, |P.rowNorm t| ∂unitμ = ∫ t, P.rowNorm t ∂unitμ :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => abs_of_nonneg (P.rowNorm_nonneg t))
  rw [habs, P.integral_rowNorm_sq] at h
  exact h

/-- **Two edges at a vertex and a disjoint edge**: for distinct `a,b,c` and an edge `s(x,z)`
disjoint from them, `∫ |E(a,b)| |E(a,c)| |E(x,z)| ≤ ‖E‖₂³`.  Peel `b`, `c` and `z`, then
the remaining integral factors as `(∫ g²)(∫ g)`. -/
theorem cherry_edge_bound {V : Type*} [Fintype V] [DecidableEq V] {a b c x z : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxz : x ≠ z)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    ∫ y : V → ℝ, |P.resid (y a) (y b)| * |P.resid (y a) (y c)| * |P.resid (y x) (y z)|
      ∂(Measure.pi fun _ : V => unitμ) ≤ P.residL2 ^ 3 := by
  set π : Measure (V → ℝ) := Measure.pi fun _ : V => unitμ with hπ
  -- peel `b`
  have hK1 : Measurable fun y : V → ℝ => |P.resid (y a) (y c)| * |P.resid (y x) (y z)| :=
    ((P.measurable_residAt a c).abs).mul ((P.measurable_residAt x z).abs)
  have hK1nn : ∀ y : V → ℝ, 0 ≤ |P.resid (y a) (y c)| * |P.resid (y x) (y z)| :=
    fun y => by positivity
  have hK1b : ∀ y : V → ℝ, |(|P.resid (y a) (y c)| * |P.resid (y x) (y z)|)| ≤ 25 := fun y => by
    rw [abs_of_nonneg (hK1nn y)]
    nlinarith [P.abs_resid_le (y a) (y c), P.abs_resid_le (y x) (y z),
      abs_nonneg (P.resid (y a) (y c)), abs_nonneg (P.resid (y x) (y z))]
  have hK1upd : ∀ (y : V → ℝ) (s : ℝ),
      |P.resid (Function.update y b s a) (Function.update y b s c)|
        * |P.resid (Function.update y b s x) (Function.update y b s z)|
      = |P.resid (y a) (y c)| * |P.resid (y x) (y z)| := fun y s => by
    rw [Function.update_of_ne hab, Function.update_of_ne (Ne.symm hbc),
      Function.update_of_ne hxb, Function.update_of_ne hzb]
  have hstep1 := P.peel_leaf (w := b) (a := a) hab hK1 hK1b hK1nn hK1upd
  -- peel `c`
  have hK2 : Measurable fun y : V → ℝ => |P.resid (y x) (y z)| * P.rowNorm (y a) :=
    ((P.measurable_residAt x z).abs).mul (P.measurable_rowNormAt a)
  have hK2nn : ∀ y : V → ℝ, 0 ≤ |P.resid (y x) (y z)| * P.rowNorm (y a) :=
    fun y => mul_nonneg (abs_nonneg _) (P.rowNorm_nonneg _)
  have hK2b : ∀ y : V → ℝ, |(|P.resid (y x) (y z)| * P.rowNorm (y a))| ≤ 25 := fun y => by
    rw [abs_of_nonneg (hK2nn y)]
    nlinarith [P.abs_resid_le (y x) (y z), abs_nonneg (P.resid (y x) (y z)),
      P.rowNorm_le (y a), P.rowNorm_nonneg (y a)]
  have hK2upd : ∀ (y : V → ℝ) (s : ℝ),
      |P.resid (Function.update y c s x) (Function.update y c s z)|
        * P.rowNorm (Function.update y c s a)
      = |P.resid (y x) (y z)| * P.rowNorm (y a) := fun y s => by
    rw [Function.update_of_ne hxc, Function.update_of_ne hzc, Function.update_of_ne hac]
  have hstep2 := P.peel_leaf (w := c) (a := a) hac hK2 hK2b hK2nn hK2upd
  -- peel `z`
  have hK3 : Measurable fun y : V → ℝ => P.rowNorm (y a) * P.rowNorm (y a) :=
    (P.measurable_rowNormAt a).mul (P.measurable_rowNormAt a)
  have hK3nn : ∀ y : V → ℝ, 0 ≤ P.rowNorm (y a) * P.rowNorm (y a) :=
    fun y => mul_nonneg (P.rowNorm_nonneg _) (P.rowNorm_nonneg _)
  have hK3b : ∀ y : V → ℝ, |P.rowNorm (y a) * P.rowNorm (y a)| ≤ 25 := fun y => by
    rw [abs_of_nonneg (hK3nn y)]
    nlinarith [P.rowNorm_le (y a), P.rowNorm_nonneg (y a)]
  have hK3upd : ∀ (y : V → ℝ) (s : ℝ),
      P.rowNorm (Function.update y z s a) * P.rowNorm (Function.update y z s a)
      = P.rowNorm (y a) * P.rowNorm (y a) := fun y s => by
    rw [Function.update_of_ne (Ne.symm hza)]
  have hstep3 := P.peel_leaf (w := z) (a := x) hxz hK3 hK3b hK3nn hK3upd
  -- the factorised remainder
  have hfac : ∫ y : V → ℝ, P.rowNorm (y a) * P.rowNorm (y a) * P.rowNorm (y x) ∂π
      = P.residSq * ∫ t, P.rowNorm t ∂unitμ := by
    have hmp := measurePreserving_pair (V := V) (Ne.symm hxa)
    have hmeasZ : Measurable fun q : ℝ × ℝ => P.rowNorm q.1 ^ 2 * P.rowNorm q.2 :=
      (P.measurable_rowNorm.comp measurable_fst).pow_const 2 |>.mul
        (P.measurable_rowNorm.comp measurable_snd)
    calc ∫ y : V → ℝ, P.rowNorm (y a) * P.rowNorm (y a) * P.rowNorm (y x) ∂π
        = ∫ y : V → ℝ, (fun q : ℝ × ℝ => P.rowNorm q.1 ^ 2 * P.rowNorm q.2) (y a, y x) ∂π :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
      _ = ∫ q : ℝ × ℝ, P.rowNorm q.1 ^ 2 * P.rowNorm q.2 ∂(unitμ.prod unitμ) := by
          rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
            hmeasZ.aestronglyMeasurable]
      _ = (∫ t, P.rowNorm t ^ 2 ∂unitμ) * ∫ t, P.rowNorm t ∂unitμ :=
          integral_prod_mul (fun t : ℝ => P.rowNorm t ^ 2) (fun t : ℝ => P.rowNorm t)
      _ = P.residSq * ∫ t, P.rowNorm t ∂unitμ := by rw [P.integral_rowNorm_sq]
  have hre1 : ∫ y : V → ℝ, |P.resid (y a) (y b)| * |P.resid (y a) (y c)|
        * |P.resid (y x) (y z)| ∂π
      = ∫ y : V → ℝ, (|P.resid (y a) (y c)| * |P.resid (y x) (y z)|)
        * |P.resid (y a) (y b)| ∂π :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  have hre2 : ∫ y : V → ℝ, (|P.resid (y a) (y c)| * |P.resid (y x) (y z)|)
        * P.rowNorm (y a) ∂π
      = ∫ y : V → ℝ, (|P.resid (y x) (y z)| * P.rowNorm (y a))
        * |P.resid (y a) (y c)| ∂π :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  have hre3 : ∫ y : V → ℝ, (|P.resid (y x) (y z)| * P.rowNorm (y a)) * P.rowNorm (y a) ∂π
      = ∫ y : V → ℝ, (P.rowNorm (y a) * P.rowNorm (y a)) * |P.resid (y x) (y z)| ∂π :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  have hlast : P.residSq * ∫ t, P.rowNorm t ∂unitμ ≤ P.residL2 ^ 3 := by
    rw [← P.residL2_sq]
    have := P.integral_rowNorm_le
    have h0 := P.residL2_nonneg
    nlinarith [sq_nonneg P.residL2]
  rw [hre1]
  refine le_trans hstep1 (le_trans (le_of_eq hre2) (le_trans hstep2
    (le_trans (le_of_eq hre3) (le_trans hstep3 (le_trans (le_of_eq hfac) hlast)))))

end BKernel

/-! ## The combinatorial trichotomy -/

/-- The edge-set part of the classification: once a vertex `a` carries two edges of `T`, either
`T` is a star at `a`, or it contains a three-edge walk, or two edges at `a` and an edge disjoint
from them. -/
theorem star_structure_of_two_edges {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {T : Finset (Sym2 V)} (hT : T ⊆ H.edgeFinset)
    {a b : V} (hab : a ≠ b) (habT : s(a, b) ∈ T)
    (hother : ∃ e ∈ T, e ≠ s(a, b) ∧ a ∈ e) :
    (∃ u, 2 ≤ T.card ∧ ∀ e ∈ T, ∃ w, w ≠ u ∧ e = s(u, w)) ∨
    (∃ a b c v : V, s(a, b) ∈ T ∧ s(a, c) ∈ T ∧ s(b, v) ∈ T ∧
      s(a, b) ≠ s(a, c) ∧ s(a, b) ≠ s(b, v) ∧ s(a, c) ≠ s(b, v) ∧
      a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ v ≠ a ∧ v ≠ b) ∨
    (∃ a b c x z : V, s(a, b) ∈ T ∧ s(a, c) ∈ T ∧ s(x, z) ∈ T ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x ≠ z ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c) := by
  classical
  have hnd : ∀ p q : V, s(p, q) ∈ T → p ≠ q := fun p q h hpq =>
    H.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hT h)) (Sym2.mk_isDiag_iff.mpr hpq)
  obtain ⟨e₁, he₁T, he₁ne, hae₁⟩ := hother
  set c : V := Sym2.Mem.other hae₁ with hcdef
  have hc₁ : s(a, c) = e₁ := Sym2.other_spec hae₁
  have hacT : s(a, c) ∈ T := by rw [hc₁]; exact he₁T
  have hac : a ≠ c := hnd a c hacT
  have hbc : b ≠ c := by
    rintro rfl
    exact he₁ne hc₁.symm
  by_cases hwalk : ∃ a b c v : V, s(a, b) ∈ T ∧ s(a, c) ∈ T ∧ s(b, v) ∈ T ∧
      s(a, b) ≠ s(a, c) ∧ s(a, b) ≠ s(b, v) ∧ s(a, c) ≠ s(b, v) ∧
      a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ v ≠ a ∧ v ≠ b
  · exact Or.inr (Or.inl hwalk)
  -- every neighbour of `a` is a leaf
  have hleaf : ∀ w, s(a, w) ∈ T → ∀ v, s(w, v) ∈ T → v = a := by
    intro w hwT v hvT
    by_contra hva
    have haw : a ≠ w := hnd a w hwT
    have hwv : w ≠ v := hnd w v hvT
    obtain ⟨z, hzT, hzw, hza⟩ : ∃ z, s(a, z) ∈ T ∧ z ≠ w ∧ z ≠ a := by
      by_cases hbw : b = w
      · exact ⟨c, hacT, fun h => hbc (hbw.trans h.symm), fun h => hac h.symm⟩
      · exact ⟨b, habT, hbw, fun h => hab h.symm⟩
    apply hwalk
    refine ⟨a, w, z, v, hwT, hzT, hvT, ?_, ?_, ?_, haw, hza, hzw, hva, fun h => hwv h.symm⟩
    · intro h
      exact hzw (Sym2.congr_right.mp h).symm
    · intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact haw h1
      · exact hva h1.symm
    · intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact haw h1
      · exact hva h1.symm
  by_cases hstar : ∀ e ∈ T, a ∈ e
  · refine Or.inl ⟨a, ?_, fun e he => ?_⟩
    · have hne : s(a, b) ≠ s(a, c) := fun h => hbc (Sym2.congr_right.mp h)
      have hsub : ({s(a, b), s(a, c)} : Finset (Sym2 V)) ⊆ T := by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact habT
        · exact hacT
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hne] at this
    · have hae := hstar e he
      refine ⟨Sym2.Mem.other hae, fun h => ?_, (Sym2.other_spec hae).symm⟩
      have hspec : s(a, Sym2.Mem.other hae) = e := Sym2.other_spec hae
      exact hnd a _ (by rw [hspec]; exact he) h.symm
  · push Not at hstar
    obtain ⟨e, heT, hae⟩ := hstar
    revert heT hae
    induction e using Sym2.ind with
    | _ x z =>
      intro hxzT haxz
      rw [Sym2.mem_iff] at haxz
      push Not at haxz
      have hxz : x ≠ z := hnd x z hxzT
      have hzxT : s(z, x) ∈ T := by rw [Sym2.eq_swap]; exact hxzT
      refine Or.inr (Or.inr ⟨a, b, c, x, z, habT, hacT, hxzT, hab, hac, hbc, hxz,
        fun h => haxz.1 h.symm, ?_, ?_, fun h => haxz.2 h.symm, ?_, ?_⟩)
      · intro h
        rw [h] at hxzT
        exact haxz.2 (hleaf b habT z hxzT).symm
      · intro h
        rw [h] at hxzT
        exact haxz.2 (hleaf c hacT z hxzT).symm
      · intro h
        rw [h] at hzxT
        exact haxz.1 (hleaf b habT x hzxT).symm
      · intro h
        rw [h] at hzxT
        exact haxz.1 (hleaf c hacT x hzxT).symm

/-- **The classification of a nonempty edge set.**  It has an isolated edge, or is a star with
at least two edges, or contains a three-edge walk, or contains two edges at a vertex together
with an edge disjoint from them. -/
theorem exists_star_structure {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {T : Finset (Sym2 V)} (hT : T ⊆ H.edgeFinset) (hTne : T.Nonempty) :
    (∃ a b, a ≠ b ∧ s(a, b) ∈ T ∧ ∀ e ∈ T, e ≠ s(a, b) → a ∉ e ∧ b ∉ e) ∨
    (∃ u, 2 ≤ T.card ∧ ∀ e ∈ T, ∃ w, w ≠ u ∧ e = s(u, w)) ∨
    (∃ a b c v : V, s(a, b) ∈ T ∧ s(a, c) ∈ T ∧ s(b, v) ∈ T ∧
      s(a, b) ≠ s(a, c) ∧ s(a, b) ≠ s(b, v) ∧ s(a, c) ≠ s(b, v) ∧
      a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ v ≠ a ∧ v ≠ b) ∨
    (∃ a b c x z : V, s(a, b) ∈ T ∧ s(a, c) ∈ T ∧ s(x, z) ∈ T ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x ≠ z ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c) := by
  classical
  obtain ⟨e₀, he₀⟩ := hTne
  revert he₀
  induction e₀ using Sym2.ind with
  | _ p q =>
    intro hpqT
    have hpq : p ≠ q := fun h =>
      H.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hT hpqT))
        (Sym2.mk_isDiag_iff.mpr h)
    by_cases hp : ∃ e ∈ T, e ≠ s(p, q) ∧ p ∈ e
    · exact Or.inr (star_structure_of_two_edges H hT hpq hpqT hp)
    by_cases hq : ∃ e ∈ T, e ≠ s(q, p) ∧ q ∈ e
    · have hqpT : s(q, p) ∈ T := by rw [Sym2.eq_swap]; exact hpqT
      exact Or.inr (star_structure_of_two_edges H hT (Ne.symm hpq) hqpT hq)
    push Not at hp hq
    exact Or.inl ⟨p, q, hpq, hpqT, fun e he hne =>
      ⟨hp e he hne, hq e he (by rw [Sym2.eq_swap]; exact hne)⟩⟩

end UpperTailOptimizers
