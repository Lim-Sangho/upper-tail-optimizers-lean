import Mathlib

/-!
# Lower convex envelope (convex minorant) of a function on `[a,b]`

`lce a b f` is the supremum of all affine functions lying below `f` on `[a,b]`.
It is the largest convex function `≤ f` (the convex minorant), and is the
infrastructure for `lem:contact-points` of `paper/paper.tex`.

Proved here: `lce ≤ f`, convexity of `lce`, the affine-minorant bound, the
tangency lemma (an affine minorant touching `f` at an interior point is tangent),
endpoint agreement and one-sided continuity (`lce_left_eq`/`lce_right_eq`,
`lce_tendsto_left`/`lce_tendsto_right`), the detached-component contact lemmas
(`exists_left_contact`/`exists_right_contact`), and the structure theorem
`lce_affine_on_component` (the η-tilt argument, via `lce_ge_chord_compact`),
with endpoint variants `lce_eq_affine_left`/`lce_eq_affine_right`.

The final section proves **`lem:two-point-convex-minorant`** of `paper/paper.tex`
(`lce_isLeast_twoPoint`): the convex minorant at `x` is the *minimum* of the
two-point convex combinations of `f` representing `x`.  The proof does not follow
the paper's citation of Rockafellar Cor. 17.1.5 (Mathlib has no convex-envelope
API); it goes through the component structure theory above, in the
endpoint-inclusive form `lce_ge_chord_general` / `lce_eq_chord_general`.
-/

namespace UpperTailOptimizers

open Set Filter
open scoped Classical Topology

/-- Values at `x` of affine functions lying below `f` on `[a,b]`. -/
def affineMinorantVals (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {y | ∃ m c : ℝ, (∀ t ∈ Set.Icc a b, m * t + c ≤ f t) ∧ y = m * x + c}

/-- Values at `x` of the two-point convex combinations of `f` over `[a,b]` that
represent `x`, i.e. the right-hand side of `lem:two-point-convex-minorant`. -/
def twoPointVals (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {y | ∃ x₁ ∈ Set.Icc a b, ∃ x₂ ∈ Set.Icc a b, ∃ lam ∈ Set.Icc (0:ℝ) 1,
        lam * x₁ + (1 - lam) * x₂ = x ∧ y = lam * f x₁ + (1 - lam) * f x₂}

/-- The lower convex envelope (convex minorant) of `f` on `[a,b]`. -/
noncomputable def lce (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup (affineMinorantVals a b f x)

theorem affineMinorantVals_nonempty {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (x : ℝ) : (affineMinorantVals a b f x).Nonempty := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf
  exact ⟨f t₀, 0, f t₀, fun t ht => by simpa using isMinOn_iff.mp hmin t ht, by ring⟩

theorem affineMinorantVals_bddAbove {a b : ℝ} {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc a b) :
    BddAbove (affineMinorantVals a b f x) := by
  refine ⟨f x, ?_⟩
  rintro y ⟨m, c, hmin, rfl⟩
  exact hmin x hx

/-- The convex minorant lies below `f`. -/
theorem lce_le_self {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) : lce a b f x ≤ f x := by
  refine csSup_le (affineMinorantVals_nonempty hab hf x) ?_
  rintro y ⟨m, c, hmin, rfl⟩
  exact hmin x hx

/-- Any affine minorant of `f` lies below the convex minorant. -/
theorem affine_le_lce {a b : ℝ} {f : ℝ → ℝ} {m c : ℝ}
    (hmin : ∀ t ∈ Icc a b, m * t + c ≤ f t) {x : ℝ} (hx : x ∈ Icc a b) :
    m * x + c ≤ lce a b f x :=
  le_csSup (affineMinorantVals_bddAbove hx) ⟨m, c, hmin, rfl⟩

/-- The convex minorant is convex on `[a,b]`. -/
theorem convexOn_lce {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    ConvexOn ℝ (Icc a b) (lce a b f) := by
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  refine csSup_le (affineMinorantVals_nonempty hab hf (α • x + β • y)) ?_
  rintro v ⟨m, cc, hmin, rfl⟩
  have h1 : m * x + cc ≤ lce a b f x := affine_le_lce hmin hx
  have h2 : m * y + cc ≤ lce a b f y := affine_le_lce hmin hy
  have heq : m * (α • x + β • y) + cc = α * (m * x + cc) + β * (m * y + cc) := by
    simp only [smul_eq_mul]; linear_combination (-cc) * hαβ
  calc m * (α • x + β • y) + cc
      = α * (m * x + cc) + β * (m * y + cc) := heq
    _ ≤ α * lce a b f x + β * lce a b f y :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hα) (mul_le_mul_of_nonneg_left h2 hβ)
    _ = α • lce a b f x + β • lce a b f y := by simp [smul_eq_mul]

/-- An affine minorant of `f` touching `f` at an interior point `c₀` is
tangent there: its slope equals `f'(c₀)`. -/
theorem tangent_of_affineMinorant {a b : ℝ} {f : ℝ → ℝ} {m c c₀ f' : ℝ}
    (hmin : ∀ t ∈ Icc a b, m * t + c ≤ f t) (hc₀ : c₀ ∈ Ioo a b)
    (htouch : m * c₀ + c = f c₀) (hderiv : HasDerivAt f f' c₀) : f' = m := by
  have hline : HasDerivAt (fun t => m * t + c) m c₀ := by
    have h := (hasDerivAt_id c₀).const_mul m
    simpa using h.add_const c
  have hg : HasDerivAt (fun t => f t - (m * t + c)) (f' - m) c₀ := hderiv.sub hline
  have hmin' : IsLocalMin (fun t => f t - (m * t + c)) c₀ := by
    filter_upwards [Ioo_mem_nhds hc₀.1 hc₀.2] with t ht
    have hle : m * t + c ≤ f t := hmin t (Ioo_subset_Icc_self ht)
    have hz : f c₀ - (m * c₀ + c) = 0 := by rw [← htouch]; ring
    show f c₀ - (m * c₀ + c) ≤ f t - (m * t + c)
    linarith
  have hzero := hmin'.deriv_eq_zero
  rw [hg.deriv] at hzero
  linarith

/-- **Maximality of the convex minorant.**  Any convex `g ≤ f` on `[a,b]` lies below
`lce a b f` at every interior point.  (Proof: the supporting line of the convex `g`
at the interior point `x` — slope `g`'s right derivative — is an affine minorant of
`f`, so by `affine_le_lce` its value `g x` is `≤ lce x`.) -/
theorem lce_largest {a b : ℝ} {f g : ℝ → ℝ}
    (hgc : ConvexOn ℝ (Icc a b) g) (hgf : ∀ t ∈ Icc a b, g t ≤ f t)
    {x : ℝ} (hx : x ∈ Ioo a b) : g x ≤ lce a b f x := by
  have hxI : x ∈ interior (Icc a b) := by rw [interior_Icc]; exact hx
  have hxIcc : x ∈ Icc a b := Ioo_subset_Icc_self hx
  set m := derivWithin g (Ioi x) x with hm
  have hsupp : ∀ t ∈ Icc a b, m * t + (g x - m * x) ≤ g t := by
    intro t ht
    rcases lt_trichotomy t x with htx | htx | htx
    · have h1 := hgc.slope_le_leftDeriv_of_mem_interior ht hxI htx
      have h2 := hgc.leftDeriv_le_rightDeriv_of_mem_interior hxI
      rw [← hm] at h2
      have hsl : slope g t x ≤ m := le_trans h1 h2
      rw [slope_def_field] at hsl
      have hxt : 0 < x - t := by linarith
      have hkey := (div_le_iff₀ hxt).mp hsl
      linarith [hkey, mul_sub m x t]
    · subst htx; linarith
    · have h1 := hgc.rightDeriv_le_slope_of_mem_interior hxI ht htx
      rw [← hm] at h1
      rw [slope_def_field] at h1
      have hxt : 0 < t - x := by linarith
      have hkey := (le_div_iff₀ hxt).mp h1
      linarith [hkey, mul_sub m t x]
  have hmin : ∀ t ∈ Icc a b, m * t + (g x - m * x) ≤ f t :=
    fun t ht => le_trans (hsupp t ht) (hgf t ht)
  linarith [affine_le_lce hmin hxIcc]

/-- Steep-line lower bound at the left endpoint: for each `ε > 0` there is a slope
`M ≥ 0` such that the line through `(a, f a - ε)` with slope `-M` lies below `lce`
on all of `[a,b]`.  `(a, f a)` is the leftmost graph vertex, so such steep
minorants approximate `f a` at `a` while staying below `f`. -/
theorem lce_ge_line_left {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc a b, f a - ε - M * (x - a) ≤ lce a b f x := by
  have haa : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  obtain ⟨tB, _, hBmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le)
    (continuousOn_const.sub hf)
  set B := (f a - ε) - f tB
  have hBle : ∀ t ∈ Icc a b, (f a - ε) - f t ≤ B := fun t ht => isMaxOn_iff.mp hBmax t ht
  have hcA : Filter.Tendsto (fun t => (f a - ε) - f t) (𝓝[Icc a b] a) (𝓝 (-ε)) := by
    have h1 : Filter.Tendsto f (𝓝[Icc a b] a) (𝓝 (f a)) := hf a haa
    have h2 := h1.const_sub (f a - ε)
    have he : (f a - ε) - f a = -ε := by ring
    rwa [he] at h2
  have hmem : {t | (f a - ε) - f t < 0} ∈ 𝓝[Icc a b] a :=
    hcA (isOpen_Iio.mem_nhds (by simpa using hε))
  rw [mem_nhdsWithin] at hmem
  obtain ⟨u, hu_open, ha_u, hu_sub⟩ := hmem
  obtain ⟨δ, hδ0, hδ_ball⟩ := Metric.isOpen_iff.mp hu_open a ha_u
  set M := max 0 (B / δ)
  have hMnonneg : 0 ≤ M := le_max_left _ _
  have hmin : ∀ t ∈ Icc a b, (-M) * t + (M * a + (f a - ε)) ≤ f t := by
    intro t ht
    have key : (f a - ε) - f t ≤ M * (t - a) := by
      have hta : 0 ≤ t - a := by linarith [ht.1]
      by_cases hclose : t - a < δ
      · have htu : t ∈ u := by
          apply hδ_ball
          rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hta]; linarith
        have : (f a - ε) - f t < 0 := hu_sub ⟨htu, ht⟩
        linarith [mul_nonneg hMnonneg hta]
      · push Not at hclose
        have hBd : B / δ ≤ M := le_max_right _ _
        have h1 : (f a - ε) - f t ≤ B := hBle t ht
        have h2 : B ≤ M * δ := by
          rcases le_total 0 (B / δ) with hpos | hneg
          · have : B / δ * δ ≤ M * δ := mul_le_mul_of_nonneg_right hBd hδ0.le
            rwa [div_mul_cancel₀ B (ne_of_gt hδ0)] at this
          · calc B = (B / δ) * δ := by rw [div_mul_cancel₀ B (ne_of_gt hδ0)]
              _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hδ0.le
              _ ≤ M * δ := mul_nonneg hMnonneg hδ0.le
        have h3 : M * δ ≤ M * (t - a) := mul_le_mul_of_nonneg_left hclose hMnonneg
        linarith
    nlinarith [key]
  refine ⟨M, hMnonneg, fun x hx => ?_⟩
  calc f a - ε - M * (x - a) = (-M) * x + (M * a + (f a - ε)) := by ring
    _ ≤ lce a b f x := affine_le_lce hmin hx

/-- The convex minorant agrees with `f` at the left endpoint `a`. -/
theorem lce_left_eq {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    lce a b f a = f a := by
  have haa : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  refine le_antisymm (lce_le_self hab.le hf haa) (le_of_forall_pos_le_add (fun ε hε => ?_))
  obtain ⟨M, _, hM⟩ := lce_ge_line_left hab hf hε
  have hh := hM a haa
  simp only [sub_self, mul_zero, sub_zero] at hh
  linarith

/-- Steep-line lower bound at the right endpoint (mirror of `lce_ge_line_left`). -/
theorem lce_ge_line_right {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc a b, f b - ε - M * (b - x) ≤ lce a b f x := by
  have hbb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  obtain ⟨tB, _, hBmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le)
    (continuousOn_const.sub hf)
  set B := (f b - ε) - f tB
  have hBle : ∀ t ∈ Icc a b, (f b - ε) - f t ≤ B := fun t ht => isMaxOn_iff.mp hBmax t ht
  have hcB : Filter.Tendsto (fun t => (f b - ε) - f t) (𝓝[Icc a b] b) (𝓝 (-ε)) := by
    have h1 : Filter.Tendsto f (𝓝[Icc a b] b) (𝓝 (f b)) := hf b hbb
    have h2 := h1.const_sub (f b - ε)
    have he : (f b - ε) - f b = -ε := by ring
    rwa [he] at h2
  have hmem : {t | (f b - ε) - f t < 0} ∈ 𝓝[Icc a b] b :=
    hcB (isOpen_Iio.mem_nhds (by simpa using hε))
  rw [mem_nhdsWithin] at hmem
  obtain ⟨u, hu_open, hb_u, hu_sub⟩ := hmem
  obtain ⟨δ, hδ0, hδ_ball⟩ := Metric.isOpen_iff.mp hu_open b hb_u
  set M := max 0 (B / δ)
  have hMnonneg : 0 ≤ M := le_max_left _ _
  have hmin : ∀ t ∈ Icc a b, M * t + (f b - ε - M * b) ≤ f t := by
    intro t ht
    have key : (f b - ε) - f t ≤ M * (b - t) := by
      have hbt : 0 ≤ b - t := by linarith [ht.2]
      by_cases hclose : b - t < δ
      · have htu : t ∈ u := hδ_ball (by
          rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_nonneg hbt]; linarith)
        have : (f b - ε) - f t < 0 := hu_sub ⟨htu, ht⟩
        linarith [mul_nonneg hMnonneg hbt]
      · push Not at hclose
        have hBd : B / δ ≤ M := le_max_right _ _
        have h1 : (f b - ε) - f t ≤ B := hBle t ht
        have h2 : B ≤ M * δ := by
          rcases le_total 0 (B / δ) with hpos | hneg
          · have : B / δ * δ ≤ M * δ := mul_le_mul_of_nonneg_right hBd hδ0.le
            rwa [div_mul_cancel₀ B (ne_of_gt hδ0)] at this
          · calc B = (B / δ) * δ := by rw [div_mul_cancel₀ B (ne_of_gt hδ0)]
              _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hδ0.le
              _ ≤ M * δ := mul_nonneg hMnonneg hδ0.le
        have h3 : M * δ ≤ M * (b - t) := mul_le_mul_of_nonneg_left hclose hMnonneg
        linarith
    nlinarith [key]
  refine ⟨M, hMnonneg, fun x hx => ?_⟩
  calc f b - ε - M * (b - x) = M * x + (f b - ε - M * b) := by ring
    _ ≤ lce a b f x := affine_le_lce hmin hx

/-- The convex minorant agrees with `f` at the right endpoint `b`. -/
theorem lce_right_eq {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    lce a b f b = f b := by
  have hbb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  refine le_antisymm (lce_le_self hab.le hf hbb) (le_of_forall_pos_le_add (fun ε hε => ?_))
  obtain ⟨M, _, hM⟩ := lce_ge_line_right hab hf hε
  have hh := hM b hbb
  simp only [sub_self, mul_zero, sub_zero] at hh
  linarith

/-- `lce a b f` is continuous on the open interval `(a,b)` (a finite convex function). -/
theorem lce_continuousOn_Ioo {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : ContinuousOn (lce a b f) (Ioo a b) := by
  have := (convexOn_lce hab hf).continuousOn_interior
  rwa [interior_Icc] at this

/-- Left endpoint of the detached component through an interior detached point `x₀`:
there is a contact `c ∈ [a, x₀)` with `lce < f` on `(c, x₀)`.  (`c` is the supremum
of the contact set in `[a,x₀]`, which contains `a` by `lce_left_eq`.) -/
theorem exists_left_contact {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hlt : lce a b f x₀ < f x₀) :
    ∃ c, a ≤ c ∧ c < x₀ ∧ lce a b f c = f c ∧ ∀ y ∈ Ioo c x₀, lce a b f y < f y := by
  have hx₀ab : x₀ ∈ Icc a b := Ioo_subset_Icc_self hx₀
  set S := {y | y ∈ Icc a x₀ ∧ lce a b f y = f y}
  have ha_mem : a ∈ S := ⟨⟨le_refl a, le_of_lt hx₀.1⟩, lce_left_eq hab hf⟩
  have hSbdd : BddAbove S := ⟨x₀, fun y hy => hy.1.2⟩
  set c := sSup S
  have hca : a ≤ c := le_csSup hSbdd ha_mem
  have hcx₀le : c ≤ x₀ := csSup_le ⟨a, ha_mem⟩ (fun y hy => hy.1.2)
  have hlceIoo : ContinuousOn (lce a b f) (Ioo a b) := lce_continuousOn_Ioo hab.le hf
  -- `lce - f < 0` on a ball around `x₀`
  have hgc : ContinuousAt (fun y => lce a b f y - f y) x₀ :=
    (hlceIoo.continuousAt (Ioo_mem_nhds hx₀.1 hx₀.2)).sub
      (hf.continuousAt (Icc_mem_nhds hx₀.1 hx₀.2))
  have hgx₀ : lce a b f x₀ - f x₀ < 0 := by linarith
  have hmemη : {y | lce a b f y - f y < 0} ∈ 𝓝 x₀ :=
    hgc (isOpen_Iio.mem_nhds hgx₀)
  obtain ⟨η, hη0, hηball⟩ := Metric.mem_nhds_iff.mp hmemη
  -- every `y ∈ S` is `≤ x₀ - η`, so `c < x₀`
  have hSfar : ∀ y ∈ S, y ≤ x₀ - η := by
    intro y hy
    by_contra hcon
    push Not at hcon
    have hyx₀ : y ≤ x₀ := hy.1.2
    have : y ∈ Metric.ball x₀ η := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    have : lce a b f y - f y < 0 := hηball this
    have := hy.2  -- lce y = f y
    linarith
  have hcx₀ : c < x₀ := lt_of_le_of_lt (csSup_le ⟨a, ha_mem⟩ hSfar) (by linarith)
  -- `c ∈ closure S`
  have hc_closure : c ∈ closure S := by
    rw [mem_closure_iff]
    intro o ho hco
    obtain ⟨ε, hε0, hεsub⟩ := Metric.isOpen_iff.mp ho c hco
    obtain ⟨y, hyS, hylt⟩ := exists_lt_of_lt_csSup ⟨a, ha_mem⟩ (show c - ε < c by linarith)
    have hyc : y ≤ c := le_csSup hSbdd hyS
    refine ⟨y, hεsub ?_, hyS⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]; linarith
  -- `lce c = f c`
  have hcontact : lce a b f c = f c := by
    rcases eq_or_lt_of_le hca with hca_eq | hca_lt
    · rw [← hca_eq]; exact lce_left_eq hab hf
    · have hc_ioo : c ∈ Ioo a b := ⟨hca_lt, lt_trans hcx₀ hx₀.2⟩
      have hgcc : ContinuousAt (fun y => lce a b f y - f y) c :=
        (hlceIoo.continuousAt (Ioo_mem_nhds hc_ioo.1 hc_ioo.2)).sub
          (hf.continuousAt (Icc_mem_nhds hc_ioo.1 hc_ioo.2))
      obtain ⟨s, hsS, hslim⟩ := mem_closure_iff_seq_limit.mp hc_closure
      have hT : Filter.Tendsto (fun y => lce a b f y - f y) (𝓝 c)
          (𝓝 (lce a b f c - f c)) := hgcc
      have hlim := hT.comp hslim
      have heq0 : (fun y => lce a b f y - f y) ∘ s = (fun _ => (0:ℝ)) := by
        funext n; simp only [Function.comp_apply]; have := (hsS n).2; linarith
      rw [heq0] at hlim
      have := tendsto_nhds_unique hlim tendsto_const_nhds
      linarith
  -- `lce < f` on `(c, x₀)`
  refine ⟨c, hca, hcx₀, hcontact, fun y hy => ?_⟩
  have hyIcc : y ∈ Icc a x₀ := ⟨le_trans hca (le_of_lt hy.1), le_of_lt hy.2⟩
  have hyle : lce a b f y ≤ f y := lce_le_self hab.le hf ⟨hyIcc.1, le_trans hyIcc.2 hx₀ab.2⟩
  rcases eq_or_lt_of_le hyle with heq | hlt'
  · exfalso
    have hyS : y ∈ S := ⟨hyIcc, heq⟩
    have : y ≤ c := le_csSup hSbdd hyS
    linarith [hy.1]
  · exact hlt'

/-- `lce a b f` is right-continuous at the left endpoint `a` (value `f a`), by the
squeeze `f a - ε - M(x-a) ≤ lce x ≤ f x` from `lce_ge_line_left` and `lce_le_self`. -/
theorem lce_tendsto_left {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Filter.Tendsto (lce a b f) (𝓝[Ioo a b] a) (𝓝 (f a)) := by
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨M, hM0, hM⟩ := lce_ge_line_left hab hf (show (0:ℝ) < (f a - c) / 2 by linarith)
    have hMt : Filter.Tendsto (fun x => M * (x - a)) (𝓝[Ioo a b] a) (𝓝 0) := by
      have : Filter.Tendsto (fun x : ℝ => M * (x - a)) (𝓝 a) (𝓝 (M * (a - a))) := by
        have hcont : Continuous (fun x : ℝ => M * (x - a)) := by fun_prop
        exact hcont.tendsto a
      simp only [sub_self, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ x in 𝓝[Ioo a b] a, M * (x - a) < (f a - c) / 2 :=
      hMt (isOpen_Iio.mem_nhds (show (0:ℝ) < (f a - c) / 2 by linarith))
    filter_upwards [hev, self_mem_nhdsWithin] with x hx hxmem
    have := hM x (Ioo_subset_Icc_self hxmem)
    linarith
  · have hcont : Filter.Tendsto f (𝓝[Ioo a b] a) (𝓝 (f a)) :=
      ((hf a (left_mem_Icc.mpr hab.le)).mono Ioo_subset_Icc_self)
    have hev : ∀ᶠ x in 𝓝[Ioo a b] a, f x < c := hcont (isOpen_Iio.mem_nhds hc)
    filter_upwards [hev, self_mem_nhdsWithin] with x hx hxmem
    have := lce_le_self hab.le hf (Ioo_subset_Icc_self hxmem)
    linarith

/-- `lce a b f` is left-continuous at the right endpoint `b` (mirror). -/
theorem lce_tendsto_right {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Filter.Tendsto (lce a b f) (𝓝[Ioo a b] b) (𝓝 (f b)) := by
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨M, hM0, hM⟩ := lce_ge_line_right hab hf (show (0:ℝ) < (f b - c) / 2 by linarith)
    have hMt : Filter.Tendsto (fun x => M * (b - x)) (𝓝[Ioo a b] b) (𝓝 0) := by
      have : Filter.Tendsto (fun x : ℝ => M * (b - x)) (𝓝 b) (𝓝 (M * (b - b))) := by
        have hcont : Continuous (fun x : ℝ => M * (b - x)) := by fun_prop
        exact hcont.tendsto b
      simp only [sub_self, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ x in 𝓝[Ioo a b] b, M * (b - x) < (f b - c) / 2 :=
      hMt (isOpen_Iio.mem_nhds (show (0:ℝ) < (f b - c) / 2 by linarith))
    filter_upwards [hev, self_mem_nhdsWithin] with x hx hxmem
    have := hM x (Ioo_subset_Icc_self hxmem)
    linarith
  · have hcont : Filter.Tendsto f (𝓝[Ioo a b] b) (𝓝 (f b)) :=
      ((hf b (right_mem_Icc.mpr hab.le)).mono Ioo_subset_Icc_self)
    have hev : ∀ᶠ x in 𝓝[Ioo a b] b, f x < c := hcont (isOpen_Iio.mem_nhds hc)
    filter_upwards [hev, self_mem_nhdsWithin] with x hx hxmem
    have := lce_le_self hab.le hf (Ioo_subset_Icc_self hxmem)
    linarith

/-- Right endpoint of the detached component (mirror of `exists_left_contact`). -/
theorem exists_right_contact {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hlt : lce a b f x₀ < f x₀) :
    ∃ d, x₀ < d ∧ d ≤ b ∧ lce a b f d = f d ∧ ∀ y ∈ Ioo x₀ d, lce a b f y < f y := by
  have hx₀ab : x₀ ∈ Icc a b := Ioo_subset_Icc_self hx₀
  set S := {y | y ∈ Icc x₀ b ∧ lce a b f y = f y}
  have hb_mem : b ∈ S := ⟨⟨le_of_lt hx₀.2, le_refl b⟩, lce_right_eq hab hf⟩
  have hSbdd : BddBelow S := ⟨x₀, fun y hy => hy.1.1⟩
  set d := sInf S
  have hdb : d ≤ b := csInf_le hSbdd hb_mem
  have hx₀d : x₀ ≤ d := le_csInf ⟨b, hb_mem⟩ (fun y hy => hy.1.1)
  have hlceIoo : ContinuousOn (lce a b f) (Ioo a b) := lce_continuousOn_Ioo hab.le hf
  have hgc : ContinuousAt (fun y => lce a b f y - f y) x₀ :=
    (hlceIoo.continuousAt (Ioo_mem_nhds hx₀.1 hx₀.2)).sub
      (hf.continuousAt (Icc_mem_nhds hx₀.1 hx₀.2))
  have hgx₀ : lce a b f x₀ - f x₀ < 0 := by linarith
  have hmemη : {y | lce a b f y - f y < 0} ∈ 𝓝 x₀ := hgc (isOpen_Iio.mem_nhds hgx₀)
  obtain ⟨η, hη0, hηball⟩ := Metric.mem_nhds_iff.mp hmemη
  have hSfar : ∀ y ∈ S, x₀ + η ≤ y := by
    intro y hy
    by_contra hcon
    push Not at hcon
    have hx₀y : x₀ ≤ y := hy.1.1
    have : y ∈ Metric.ball x₀ η := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    have : lce a b f y - f y < 0 := hηball this
    have := hy.2
    linarith
  have hx₀d' : x₀ < d := lt_of_lt_of_le (by linarith) (le_csInf ⟨b, hb_mem⟩ hSfar)
  have hd_closure : d ∈ closure S := by
    rw [mem_closure_iff]
    intro o ho hdo
    obtain ⟨ε, hε0, hεsub⟩ := Metric.isOpen_iff.mp ho d hdo
    obtain ⟨y, hyS, hylt⟩ := exists_lt_of_csInf_lt ⟨b, hb_mem⟩ (show d < d + ε by linarith)
    have hdy : d ≤ y := csInf_le hSbdd hyS
    refine ⟨y, hεsub ?_, hyS⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
  have hcontact : lce a b f d = f d := by
    rcases eq_or_lt_of_le hdb with hdb_eq | hdb_lt
    · rw [hdb_eq]; exact lce_right_eq hab hf
    · have hd_ioo : d ∈ Ioo a b := ⟨lt_trans hx₀.1 hx₀d', hdb_lt⟩
      have hgcc : ContinuousAt (fun y => lce a b f y - f y) d :=
        (hlceIoo.continuousAt (Ioo_mem_nhds hd_ioo.1 hd_ioo.2)).sub
          (hf.continuousAt (Icc_mem_nhds hd_ioo.1 hd_ioo.2))
      obtain ⟨s, hsS, hslim⟩ := mem_closure_iff_seq_limit.mp hd_closure
      have hT : Filter.Tendsto (fun y => lce a b f y - f y) (𝓝 d)
          (𝓝 (lce a b f d - f d)) := hgcc
      have hlim := hT.comp hslim
      have heq0 : (fun y => lce a b f y - f y) ∘ s = (fun _ => (0:ℝ)) := by
        funext n; simp only [Function.comp_apply]; have := (hsS n).2; linarith
      rw [heq0] at hlim
      have := tendsto_nhds_unique hlim tendsto_const_nhds
      linarith
  refine ⟨d, hx₀d', hdb, hcontact, fun y hy => ?_⟩
  have hyIcc : y ∈ Icc x₀ b := ⟨le_of_lt hy.1, le_trans (le_of_lt hy.2) hdb⟩
  have hyle : lce a b f y ≤ f y := lce_le_self hab.le hf ⟨le_trans hx₀ab.1 hyIcc.1, hyIcc.2⟩
  rcases eq_or_lt_of_le hyle with heq | hlt'
  · exfalso
    have hyS : y ∈ S := ⟨hyIcc, heq⟩
    have : d ≤ y := csInf_le hSbdd hyS
    linarith [hy.2]
  · exact hlt'

/-- The convex minorant lies below its own chord over `[c,d]` (the easy half of the
structure theorem), since `lce` is convex. -/
theorem lce_le_chord {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {c d : ℝ} (hcd : c < d) (hac : a ≤ c) (hdb : d ≤ b) {x : ℝ} (hx : x ∈ Icc c d) :
    lce a b f x ≤ lce a b f c + ((lce a b f d - lce a b f c) / (d - c)) * (x - c) := by
  have hcb : c ∈ Icc a b := ⟨hac, le_trans hcd.le hdb⟩
  have hdb' : d ∈ Icc a b := ⟨le_trans hac hcd.le, hdb⟩
  set α := (d - x) / (d - c) with hα
  set β := (x - c) / (d - c) with hβ
  have hdc : 0 < d - c := by linarith
  have hdcne : d - c ≠ 0 := ne_of_gt hdc
  have hαβ : α + β = 1 := by rw [hα, hβ, ← add_div, div_eq_one_iff_eq hdcne]; ring
  have hα0 : 0 ≤ α := by rw [hα]; apply div_nonneg (by linarith [hx.2]) hdc.le
  have hβ0 : 0 ≤ β := by rw [hβ]; apply div_nonneg (by linarith [hx.1]) hdc.le
  have hxeq : α • c + β • d = x := by
    simp only [smul_eq_mul, hα, hβ]; field_simp; ring
  have hconv := (convexOn_lce hab hf).2 hcb hdb' hα0 hβ0 hαβ
  rw [hxeq] at hconv
  -- `α • lce c + β • lce d = chord(x)`
  have hchord : α • lce a b f c + β • lce a b f d
      = lce a b f c + ((lce a b f d - lce a b f c) / (d - c)) * (x - c) := by
    simp only [smul_eq_mul, hα, hβ]; field_simp; ring
  rw [hchord] at hconv
  exact hconv

/- The reverse (`≥`) half of the structure theorem (`lce_ge_chord_on_component`)
follows from the η-tilt variational argument.  Its key step is `lce_ge_chord_compact`
below: on a compact subinterval `[c',d'] ⊂ (c,d)`, the convex minorant equals its
chord, proved by perturbing `lce` toward the chord and contradicting maximality
(`lce_largest`).  The convexity of the perturbation is obtained cleanly via
`ConvexOn.sup`, using that the chord lies below `lce` outside `[c',d']`
(`chord_le_lce_outside`). -/

/-- An affine function is convex on any convex set. -/
theorem convexOn_affine (s : Set ℝ) (hs : Convex ℝ s) (m k : ℝ) :
    ConvexOn ℝ s (fun t => m * t + k) := by
  refine ⟨hs, fun x _ y _ p q _ _ hpq => ?_⟩
  simp only [smul_eq_mul]
  have heq : m * (p * x + q * y) + k = p * (m * x + k) + q * (m * y + k) := by
    linear_combination (-k) * hpq
  exact le_of_eq heq

/-- A convex function lies above the extension of its chord over `[c',d']` outside
that interval: for `t ∉ [c',d']` (within the domain), `chord(t) ≤ lce(t)`. -/
theorem chord_le_lce_outside {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {c' d' : ℝ} (hc'd' : c' < d')
    (hc' : c' ∈ Icc a b) (hd' : d' ∈ Icc a b) {t : ℝ} (ht : t ∈ Icc a b)
    (htout : t < c' ∨ d' < t) :
    lce a b f c' + ((lce a b f d' - lce a b f c') / (d' - c')) * (t - c') ≤ lce a b f t := by
  have hconv := convexOn_lce hab hf
  have hd'c' : 0 < d' - c' := by linarith
  have hne : d' - c' ≠ (0:ℝ) := ne_of_gt hd'c'
  rcases htout with htl | htr
  · have hsl := hconv.slope_mono_adjacent ht hd' htl hc'd'
    have hct : 0 < c' - t := by linarith
    have h2 := (div_le_iff₀ hct).mp hsl
    have key : ((lce a b f d' - lce a b f c') / (d' - c')) * (t - c')
        = -(((lce a b f d' - lce a b f c') / (d' - c')) * (c' - t)) := by ring
    rw [key]; linarith [h2]
  · have hsl := hconv.slope_mono_adjacent hc' ht hc'd' htr
    have htd : 0 < t - d' := by linarith
    have h2 := (le_div_iff₀ htd).mp hsl
    have hSdc : ((lce a b f d' - lce a b f c') / (d' - c')) * (d' - c')
        = lce a b f d' - lce a b f c' := by field_simp
    have key : lce a b f c' + ((lce a b f d' - lce a b f c') / (d' - c')) * (t - c')
        = lce a b f d' + ((lce a b f d' - lce a b f c') / (d' - c')) * (t - d') := by
      have hsplit : ((lce a b f d' - lce a b f c') / (d' - c')) * (t - c')
          = ((lce a b f d' - lce a b f c') / (d' - c')) * (d' - c')
            + ((lce a b f d' - lce a b f c') / (d' - c')) * (t - d') := by ring
      rw [hsplit, hSdc]; ring
    rw [key]; linarith [h2]

/-- **Max-trick helper.**  On a compact subinterval `[c',d'] ⊂ (c,d)`, the convex
minorant lies above its own chord (hence, with `lce_le_chord`, equals it). -/
theorem lce_ge_chord_compact {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {c d : ℝ} (hcd : c < d) (hac : a ≤ c) (hdb : d ≤ b)
    (hcomp : ∀ x ∈ Ioo c d, lce a b f x < f x)
    {c' d' : ℝ} (hcc' : c < c') (hc'd' : c' < d') (hd'd : d' < d) :
    ∀ x ∈ Icc c' d',
      lce a b f c' + ((lce a b f d' - lce a b f c') / (d' - c')) * (x - c') ≤ lce a b f x := by
  have hab : a ≤ b := le_trans hac (le_trans hcd.le hdb)
  set s' := (lce a b f d' - lce a b f c') / (d' - c') with hs'
  set C' : ℝ → ℝ := fun t => lce a b f c' + s' * (t - c') with hC'def
  have hsub_ab : Icc c' d' ⊆ Icc a b := fun y hy =>
    ⟨le_trans hac (le_of_lt (lt_of_lt_of_le hcc' hy.1)),
     le_trans (le_of_lt (lt_of_le_of_lt hy.2 hd'd)) hdb⟩
  have hsub_oo : Icc c' d' ⊆ Ioo c d := fun y hy =>
    ⟨lt_of_lt_of_le hcc' hy.1, lt_of_le_of_lt hy.2 hd'd⟩
  have hc'ab : c' ∈ Icc a b := hsub_ab ⟨le_refl _, le_of_lt hc'd'⟩
  have hd'ab : d' ∈ Icc a b := hsub_ab ⟨le_of_lt hc'd', le_refl _⟩
  have hlce_cont : ContinuousOn (lce a b f) (Icc c' d') := by
    apply (convexOn_lce hab hf).continuousOn_interior.mono
    rw [interior_Icc]
    intro y hy
    exact ⟨lt_of_lt_of_le (lt_of_le_of_lt hac hcc') hy.1,
           lt_of_le_of_lt hy.2 (lt_of_lt_of_le hd'd hdb)⟩
  have hfmlce_cont : ContinuousOn (fun t => f t - lce a b f t) (Icc c' d') :=
    (hf.mono hsub_ab).sub hlce_cont
  obtain ⟨tρ, htρ, hρmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (le_of_lt hc'd')) hfmlce_cont
  set ρ := f tρ - lce a b f tρ with hρdef
  have hρpos : 0 < ρ := by have := hcomp tρ (hsub_oo htρ); rw [hρdef]; linarith
  have hρle : ∀ t ∈ Icc c' d', ρ ≤ f t - lce a b f t := fun t ht => isMinOn_iff.mp hρmin t ht
  intro x hx
  show C' x ≤ lce a b f x
  by_contra hlt
  push Not at hlt
  have hdc'ne : d' - c' ≠ (0:ℝ) := ne_of_gt (by linarith)
  have hxoo : x ∈ Ioo c' d' := by
    refine ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
    · intro he
      rw [← he] at hlt
      simp only [hC'def, sub_self, mul_zero, add_zero] at hlt
      exact lt_irrefl _ hlt
    · intro he
      rw [he] at hlt
      have hCd' : C' d' = lce a b f d' := by
        simp only [hC'def, hs']
        field_simp
        ring
      rw [hCd'] at hlt
      exact lt_irrefl _ hlt
  have hC'convex : ConvexOn ℝ (Icc a b) C' := by
    have hCeq : C' = fun t => s' * t + (lce a b f c' - s' * c') := by
      funext t; simp only [hC'def]; ring
    rw [hCeq]; exact convexOn_affine (Icc a b) (convex_Icc a b) s' (lce a b f c' - s' * c')
  have hC'cont : ContinuousOn (fun t => C' t - lce a b f t) (Icc c' d') :=
    (hC'convex.continuousOn_interior.mono (by
      rw [interior_Icc]; intro y hy
      exact ⟨lt_of_lt_of_le (lt_of_le_of_lt hac hcc') hy.1,
             lt_of_le_of_lt hy.2 (lt_of_lt_of_le hd'd hdb)⟩)).sub hlce_cont
  obtain ⟨tM, htM, hMmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (le_of_lt hc'd')) hC'cont
  set M := C' tM - lce a b f tM
  have hMpos : 0 < M := by
    have : C' x - lce a b f x ≤ M := isMaxOn_iff.mp hMmax x hx
    linarith
  have hMle : ∀ t ∈ Icc c' d', C' t - lce a b f t ≤ M := fun t ht => isMaxOn_iff.mp hMmax t ht
  set η := min (ρ / M) 1
  have hηpos : 0 < η := lt_min (div_pos hρpos hMpos) one_pos
  have hηle1 : η ≤ 1 := min_le_right _ _
  have hηM : η * M ≤ ρ := by
    have hle : η ≤ ρ / M := min_le_left _ _
    calc η * M ≤ (ρ / M) * M := mul_le_mul_of_nonneg_right hle (le_of_lt hMpos)
      _ = ρ := by field_simp
  set h : ℝ → ℝ := fun t => (1 - η) * lce a b f t + η * C' t with hhdef
  have hh_conv : ConvexOn ℝ (Icc a b) h := by
    rw [hhdef]
    exact ((convexOn_lce hab hf).smul (by linarith : (0:ℝ) ≤ 1 - η)).add
      (hC'convex.smul (le_of_lt hηpos))
  have hg_conv : ConvexOn ℝ (Icc a b) (fun t => lce a b f t ⊔ h t) :=
    (convexOn_lce hab hf).sup hh_conv
  have hg_le : ∀ t ∈ Icc a b, lce a b f t ⊔ h t ≤ f t := by
    intro t ht
    refine max_le (lce_le_self hab hf ht) ?_
    by_cases htin : t ∈ Icc c' d'
    · have h2 : C' t - lce a b f t ≤ M := hMle t htin
      have h3 : ρ ≤ f t - lce a b f t := hρle t htin
      have h4 : η * (C' t - lce a b f t) ≤ η * M := mul_le_mul_of_nonneg_left h2 hηpos.le
      have h5 : h t = lce a b f t + η * (C' t - lce a b f t) := by rw [hhdef]; ring
      rw [h5]; linarith [h4, hηM, h3]
    · have htout : t < c' ∨ d' < t := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at htin; tauto
      have hCle : C' t ≤ lce a b f t := chord_le_lce_outside hab hf hc'd' hc'ab hd'ab ht htout
      have hhle : h t ≤ lce a b f t := by
        have h5 : h t = lce a b f t + η * (C' t - lce a b f t) := by rw [hhdef]; ring
        rw [h5]; nlinarith [hCle, hηpos.le]
      exact le_trans hhle (lce_le_self hab hf ht)
  have hxoo_ab : x ∈ Ioo a b :=
    ⟨lt_of_lt_of_le (lt_of_le_of_lt hac hcc') (le_of_lt hxoo.1),
     lt_of_lt_of_le (lt_trans hxoo.2 hd'd) hdb⟩
  have hlarge := lce_largest hg_conv hg_le hxoo_ab
  have hgx : lce a b f x < lce a b f x ⊔ h x := by
    have hhx : lce a b f x < h x := by
      have h5 : h x = lce a b f x + η * (C' x - lce a b f x) := by rw [hhdef]; ring
      rw [h5]; nlinarith [hηpos, hlt]
    exact lt_of_lt_of_le hhx (le_max_right _ _)
  linarith [hlarge, hgx]

/-- The reverse (`≥`) half of the structure theorem.  The hard variational
kernel `lce_ge_chord_compact` (above) gives `lce = chord` on every compact
`[c',d'] ⊂ (c,d)`; taking `c' ↓ c`, `d' ↑ d` and using one-sided continuity of `lce` at
the component endpoints (lower semicontinuity of the sup-of-affine `lce`, squeezed by the
continuous `f` it touches at `c`,`d`) gives `lce = chord` on `[c,d]`. -/
theorem lce_ge_chord_on_component {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {c d : ℝ} (hcd : c < d) (hac : a < c) (hdb : d < b)
    (hcomp : ∀ x ∈ Ioo c d, lce a b f x < f x)
    (_hc : lce a b f c = f c) (_hd : lce a b f d = f d) :
    ∀ x ∈ Icc c d,
      lce a b f c + ((lce a b f d - lce a b f c) / (d - c)) * (x - c) ≤ lce a b f x := by
  have hab : a ≤ b := le_trans hac.le (le_trans hcd.le hdb.le)
  have hdcpos : (0:ℝ) < d - c := by linarith
  have hdcne : d - c ≠ 0 := ne_of_gt hdcpos
  have hcc : c ∈ Ioo a b := ⟨hac, lt_trans hcd hdb⟩
  have hdd : d ∈ Ioo a b := ⟨lt_trans hac hcd, hdb⟩
  -- `lce` is continuous at every interior point
  have hcontAt : ∀ y ∈ Ioo a b, ContinuousAt (lce a b f) y := by
    intro y hy
    have hco : ContinuousOn (lce a b f) (Ioo a b) := by
      have := (convexOn_lce hab hf).continuousOn_interior
      rwa [interior_Icc] at this
    exact hco.continuousAt (IsOpen.mem_nhds isOpen_Ioo hy)
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxc | hxc
  · rw [← hxc]; simp
  rcases eq_or_lt_of_le hx.2 with hxd | hxd
  · have hval : ((lce a b f d - lce a b f c) / (d - c)) * (d - c) = lce a b f d - lce a b f c := by
      field_simp
    rw [hxd]; linarith [hval]
  -- interior case `c < x < d`: take `c' = c+t ↓ c`, `d' = d-t ↑ d`
  have hδ : (0:ℝ) < min (x - c) (d - x) := lt_min (by linarith) (by linarith)
  set g : ℝ → ℝ := fun t => lce a b f (c + t) +
    ((lce a b f (d - t) - lce a b f (c + t)) / ((d - t) - (c + t))) * (x - (c + t)) with hg
  have hgle : ∀ᶠ t in 𝓝[>] (0:ℝ), g t ≤ lce a b f x := by
    filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0:ℝ)) (Iio_mem_nhds hδ)] with t ht
    have ht0 : 0 < t := ht.1
    have htδ : t < min (x - c) (d - x) := ht.2
    have hcc' : c < c + t := by linarith
    have hc'x : c + t < x := by linarith [lt_of_lt_of_le htδ (min_le_left _ _)]
    have hxd' : x < d - t := by linarith [lt_of_lt_of_le htδ (min_le_right _ _)]
    have hd'd : d - t < d := by linarith
    have hc'd' : c + t < d - t := lt_trans hc'x hxd'
    have hxmem : x ∈ Icc (c + t) (d - t) := ⟨le_of_lt hc'x, le_of_lt hxd'⟩
    exact lce_ge_chord_compact hf hcd hac.le hdb.le hcomp hcc' hc'd' hd'd x hxmem
  have hgtend : Filter.Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (lce a b f c +
      ((lce a b f d - lce a b f c) / (d - c)) * (x - c))) := by
    have hct : Filter.Tendsto (fun t : ℝ => c + t) (𝓝 (0:ℝ)) (𝓝 c) := by
      have hcont : Continuous (fun t : ℝ => c + t) := by fun_prop
      have := hcont.tendsto (0:ℝ); simpa using this
    have hdt : Filter.Tendsto (fun t : ℝ => d - t) (𝓝 (0:ℝ)) (𝓝 d) := by
      have hcont : Continuous (fun t : ℝ => d - t) := by fun_prop
      have := hcont.tendsto (0:ℝ); simpa using this
    have hlc : Filter.Tendsto (fun t => lce a b f (c + t)) (𝓝 (0:ℝ)) (𝓝 (lce a b f c)) :=
      (hcontAt c hcc).tendsto.comp hct
    have hld : Filter.Tendsto (fun t => lce a b f (d - t)) (𝓝 (0:ℝ)) (𝓝 (lce a b f d)) :=
      (hcontAt d hdd).tendsto.comp hdt
    have hden : Filter.Tendsto (fun t : ℝ => (d - t) - (c + t)) (𝓝 (0:ℝ)) (𝓝 (d - c)) := by
      have hcont : Continuous (fun t : ℝ => (d - t) - (c + t)) := by fun_prop
      have := hcont.tendsto (0:ℝ); simpa using this
    have hxnum : Filter.Tendsto (fun t : ℝ => x - (c + t)) (𝓝 (0:ℝ)) (𝓝 (x - c)) := by
      have hcont : Continuous (fun t : ℝ => x - (c + t)) := by fun_prop
      have := hcont.tendsto (0:ℝ); simpa using this
    have htend : Filter.Tendsto g (𝓝 (0:ℝ)) (𝓝 (lce a b f c +
        ((lce a b f d - lce a b f c) / (d - c)) * (x - c))) := by
      rw [hg]
      exact hlc.add (((hld.sub hlc).div hden hdcne).mul hxnum)
    exact htend.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hgtend hgle

/-- **Structure theorem.**  On a connected component `(c,d)` of the detached set
`{x | lce a b f x < f x}` (with `lce = f` at the endpoints), the convex minorant is
affine.  The `≤`-half is `lce_le_chord`; the reverse is the η-tilt variational
argument (isolated as `lce_ge_chord_on_component`). -/
theorem lce_affine_on_component {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {c d : ℝ} (hcd : c < d) (hac : a < c) (hdb : d < b)
    (hcomp : ∀ x ∈ Ioo c d, lce a b f x < f x)
    (hc : lce a b f c = f c) (hd : lce a b f d = f d) :
    ∀ x ∈ Icc c d,
      lce a b f x = lce a b f c + ((lce a b f d - lce a b f c) / (d - c)) * (x - c) := by
  have hab : a ≤ b := le_trans hac.le (le_trans hcd.le hdb.le)
  intro x hx
  refine le_antisymm (lce_le_chord hab hf hcd hac.le hdb.le hx) ?_
  exact lce_ge_chord_on_component hf hcd hac hdb hcomp hc hd x hx

/-- On a detached component `(a, d')` reaching the **left** endpoint `a` of the
domain, the convex minorant is affine with intercept `f a`:
`lce a b f x = f a + s·(x - a)`.  Affineness comes from `lce_ge_chord_compact` +
`lce_le_chord` on compact subintervals; the intercept `f a` comes from
`lce_tendsto_left`. -/
theorem lce_eq_affine_left {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {d' : ℝ} (had' : a < d') (hd'b : d' ≤ b)
    (hcomp : ∀ x ∈ Ioo a d', lce a b f x < f x) :
    ∃ s : ℝ, ∀ x ∈ Ioo a d', lce a b f x = f a + s * (x - a) := by
  have hab' : a ≤ b := hab.le
  set p₁ := a + (d' - a) / 3 with hp₁def
  set p₂ := a + 2 * (d' - a) / 3 with hp₂def
  have hp₁mem : p₁ ∈ Ioo a d' := ⟨by rw [hp₁def]; linarith, by rw [hp₁def]; linarith⟩
  have hp₂mem : p₂ ∈ Ioo a d' := ⟨by rw [hp₂def]; linarith, by rw [hp₂def]; linarith⟩
  have hp₁₂ : p₁ < p₂ := by rw [hp₁def, hp₂def]; linarith
  set s := (lce a b f p₂ - lce a b f p₁) / (p₂ - p₁) with hsdef
  -- Affine pairing: for any two points in the component, the lce-difference is `s·Δ`.
  have hpair : ∀ x ∈ Ioo a d', ∀ y ∈ Ioo a d', lce a b f y - lce a b f x = s * (y - x) := by
    intro x hx y hy
    set lo := (a + min (min x y) (min p₁ p₂)) / 2 with hlodef
    set hi := (max (max x y) (max p₁ p₂) + d') / 2 with hhidef
    have hm_gt_a : a < min (min x y) (min p₁ p₂) := by
      simp only [lt_min_iff]; exact ⟨⟨hx.1, hy.1⟩, ⟨hp₁mem.1, hp₂mem.1⟩⟩
    have hM_lt_d : max (max x y) (max p₁ p₂) < d' := by
      simp only [max_lt_iff]; exact ⟨⟨hx.2, hy.2⟩, ⟨hp₁mem.2, hp₂mem.2⟩⟩
    have hlo_gt_a : a < lo := by rw [hlodef]; linarith
    have hhi_lt_d : hi < d' := by rw [hhidef]; linarith
    have hlo_le_min : lo ≤ min (min x y) (min p₁ p₂) := by rw [hlodef]; linarith
    have hmax_le_hi : max (max x y) (max p₁ p₂) ≤ hi := by rw [hhidef]; linarith
    have hmin_lt_max : min (min x y) (min p₁ p₂) < max (max x y) (max p₁ p₂) := by
      have h1 : min (min x y) (min p₁ p₂) ≤ min p₁ p₂ := min_le_right _ _
      have h2 : min p₁ p₂ ≤ p₁ := min_le_left _ _
      have h3 : p₂ ≤ max p₁ p₂ := le_max_right _ _
      have h4 : max p₁ p₂ ≤ max (max x y) (max p₁ p₂) := le_max_right _ _
      linarith
    have hlohi : lo < hi := by linarith
    -- the four points lie in [lo, hi]
    have hmem_lo_hi : ∀ z ∈ ({x, y, p₁, p₂} : Set ℝ), z ∈ Icc lo hi := by
      intro z hz
      have hzlo : lo ≤ z := by
        refine le_trans hlo_le_min ?_
        rcases hz with h | h | h | h <;> subst h
        · exact le_trans (min_le_left _ _) (min_le_left _ _)
        · exact le_trans (min_le_left _ _) (min_le_right _ _)
        · exact le_trans (min_le_right _ _) (min_le_left _ _)
        · exact le_trans (min_le_right _ _) (min_le_right _ _)
      have hzhi : z ≤ hi := by
        refine le_trans ?_ hmax_le_hi
        rcases hz with h | h | h | h <;> subst h
        · exact le_trans (le_max_left _ _) (le_max_left _ _)
        · exact le_trans (le_max_right _ _) (le_max_left _ _)
        · exact le_trans (le_max_left _ _) (le_max_right _ _)
        · exact le_trans (le_max_right _ _) (le_max_right _ _)
      exact ⟨hzlo, hzhi⟩
    set σ := (lce a b f hi - lce a b f lo) / (hi - lo)
    -- lce = chord(lo,hi) on [lo,hi]
    have hchord : ∀ z ∈ Icc lo hi, lce a b f z = lce a b f lo + σ * (z - lo) := by
      intro z hz
      refine le_antisymm (lce_le_chord hab' hf hlohi hlo_gt_a.le (le_trans hhi_lt_d.le hd'b) hz) ?_
      exact lce_ge_chord_compact hf had' (le_refl a) hd'b hcomp hlo_gt_a hlohi hhi_lt_d z hz
    have hxv := hchord x (hmem_lo_hi x (by simp))
    have hyv := hchord y (hmem_lo_hi y (by simp))
    have hp₁v := hchord p₁ (hmem_lo_hi p₁ (by simp))
    have hp₂v := hchord p₂ (hmem_lo_hi p₂ (by simp))
    -- s = σ
    have hp₂₁ne : p₂ - p₁ ≠ 0 := by rw [hp₁def, hp₂def]; intro h; rw [hp₁def, hp₂def] at hp₁₂; linarith
    have hseq : s = σ := by
      rw [hsdef, hp₂v, hp₁v]
      field_simp
      ring
    rw [hxv, hyv, hseq]; ring
  -- intercept = f a, via continuity of lce at the left endpoint
  have hsub : Ioo a d' ⊆ Ioo a b := fun z hz => ⟨hz.1, lt_of_lt_of_le hz.2 hd'b⟩
  have hL1 : Filter.Tendsto (lce a b f) (𝓝[Ioo a d'] a) (𝓝 (f a)) :=
    (lce_tendsto_left hab hf).mono_left (nhdsWithin_mono a hsub)
  -- on the component, lce agrees with the affine map g
  have hg_eq : ∀ x ∈ Ioo a d', lce a b f x = lce a b f p₁ + s * (x - p₁) := by
    intro x hx
    have := hpair p₁ hp₁mem x hx
    linarith
  have hcontg : Continuous (fun t : ℝ => lce a b f p₁ + s * (t - p₁)) := by fun_prop
  have hL2g : Filter.Tendsto (fun t : ℝ => lce a b f p₁ + s * (t - p₁))
      (𝓝[Ioo a d'] a) (𝓝 (lce a b f p₁ + s * (a - p₁))) :=
    (hcontg.tendsto a).mono_left nhdsWithin_le_nhds
  have hL2 : Filter.Tendsto (lce a b f) (𝓝[Ioo a d'] a)
      (𝓝 (lce a b f p₁ + s * (a - p₁))) := by
    apply hL2g.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hg_eq z hz).symm
  have hne : (𝓝[Ioo a d'] a).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt had')]
    exact left_mem_Icc.mpr had'.le
  have hfa : f a = lce a b f p₁ + s * (a - p₁) := tendsto_nhds_unique hL1 hL2
  refine ⟨s, fun x hx => ?_⟩
  rw [hg_eq x hx]
  -- lce p₁ = f a + s*(p₁ - a)
  have : lce a b f p₁ = f a + s * (p₁ - a) := by rw [hfa]; ring
  rw [this]; ring

/-- Mirror of `lce_eq_affine_left` at the **right** endpoint `b`:
`lce a b f x = f b + s·(x - b)` on a component `(c', b)` reaching `b`. -/
theorem lce_eq_affine_right {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {c' : ℝ} (hc'b : c' < b) (hac' : a ≤ c')
    (hcomp : ∀ x ∈ Ioo c' b, lce a b f x < f x) :
    ∃ s : ℝ, ∀ x ∈ Ioo c' b, lce a b f x = f b + s * (x - b) := by
  have hab' : a ≤ b := hab.le
  set p₁ := b - 2 * (b - c') / 3 with hp₁def
  set p₂ := b - (b - c') / 3 with hp₂def
  have hp₁mem : p₁ ∈ Ioo c' b := ⟨by rw [hp₁def]; linarith, by rw [hp₁def]; linarith⟩
  have hp₂mem : p₂ ∈ Ioo c' b := ⟨by rw [hp₂def]; linarith, by rw [hp₂def]; linarith⟩
  have hp₁₂ : p₁ < p₂ := by rw [hp₁def, hp₂def]; linarith
  set s := (lce a b f p₂ - lce a b f p₁) / (p₂ - p₁) with hsdef
  have hpair : ∀ x ∈ Ioo c' b, ∀ y ∈ Ioo c' b, lce a b f y - lce a b f x = s * (y - x) := by
    intro x hx y hy
    set lo := (c' + min (min x y) (min p₁ p₂)) / 2 with hlodef
    set hi := (max (max x y) (max p₁ p₂) + b) / 2 with hhidef
    have hm_gt_c : c' < min (min x y) (min p₁ p₂) := by
      simp only [lt_min_iff]; exact ⟨⟨hx.1, hy.1⟩, ⟨hp₁mem.1, hp₂mem.1⟩⟩
    have hM_lt_b : max (max x y) (max p₁ p₂) < b := by
      simp only [max_lt_iff]; exact ⟨⟨hx.2, hy.2⟩, ⟨hp₁mem.2, hp₂mem.2⟩⟩
    have hlo_gt_c : c' < lo := by rw [hlodef]; linarith
    have hhi_lt_b : hi < b := by rw [hhidef]; linarith
    have hlo_le_min : lo ≤ min (min x y) (min p₁ p₂) := by rw [hlodef]; linarith
    have hmax_le_hi : max (max x y) (max p₁ p₂) ≤ hi := by rw [hhidef]; linarith
    have hmin_lt_max : min (min x y) (min p₁ p₂) < max (max x y) (max p₁ p₂) := by
      have h1 : min (min x y) (min p₁ p₂) ≤ min p₁ p₂ := min_le_right _ _
      have h2 : min p₁ p₂ ≤ p₁ := min_le_left _ _
      have h3 : p₂ ≤ max p₁ p₂ := le_max_right _ _
      have h4 : max p₁ p₂ ≤ max (max x y) (max p₁ p₂) := le_max_right _ _
      linarith
    have hlohi : lo < hi := by linarith
    have hmem_lo_hi : ∀ z ∈ ({x, y, p₁, p₂} : Set ℝ), z ∈ Icc lo hi := by
      intro z hz
      have hzlo : lo ≤ z := by
        refine le_trans hlo_le_min ?_
        rcases hz with h | h | h | h <;> subst h
        · exact le_trans (min_le_left _ _) (min_le_left _ _)
        · exact le_trans (min_le_left _ _) (min_le_right _ _)
        · exact le_trans (min_le_right _ _) (min_le_left _ _)
        · exact le_trans (min_le_right _ _) (min_le_right _ _)
      have hzhi : z ≤ hi := by
        refine le_trans ?_ hmax_le_hi
        rcases hz with h | h | h | h <;> subst h
        · exact le_trans (le_max_left _ _) (le_max_left _ _)
        · exact le_trans (le_max_right _ _) (le_max_left _ _)
        · exact le_trans (le_max_left _ _) (le_max_right _ _)
        · exact le_trans (le_max_right _ _) (le_max_right _ _)
      exact ⟨hzlo, hzhi⟩
    set σ := (lce a b f hi - lce a b f lo) / (hi - lo)
    have hchord : ∀ z ∈ Icc lo hi, lce a b f z = lce a b f lo + σ * (z - lo) := by
      intro z hz
      refine le_antisymm (lce_le_chord hab' hf hlohi (le_trans hac' hlo_gt_c.le) hhi_lt_b.le hz) ?_
      exact lce_ge_chord_compact hf hc'b hac' (le_refl b) hcomp hlo_gt_c hlohi hhi_lt_b z hz
    have hxv := hchord x (hmem_lo_hi x (by simp))
    have hyv := hchord y (hmem_lo_hi y (by simp))
    have hp₁v := hchord p₁ (hmem_lo_hi p₁ (by simp))
    have hp₂v := hchord p₂ (hmem_lo_hi p₂ (by simp))
    have hp₂₁ne : p₂ - p₁ ≠ 0 := by intro h; linarith
    have hseq : s = σ := by rw [hsdef, hp₂v, hp₁v]; field_simp; ring
    rw [hxv, hyv, hseq]; ring
  have hsub : Ioo c' b ⊆ Ioo a b := fun z hz => ⟨lt_of_le_of_lt hac' hz.1, hz.2⟩
  have hL1 : Filter.Tendsto (lce a b f) (𝓝[Ioo c' b] b) (𝓝 (f b)) :=
    (lce_tendsto_right hab hf).mono_left (nhdsWithin_mono b hsub)
  have hg_eq : ∀ x ∈ Ioo c' b, lce a b f x = lce a b f p₁ + s * (x - p₁) := by
    intro x hx
    have := hpair p₁ hp₁mem x hx
    linarith
  have hcontg : Continuous (fun t : ℝ => lce a b f p₁ + s * (t - p₁)) := by fun_prop
  have hL2g : Filter.Tendsto (fun t : ℝ => lce a b f p₁ + s * (t - p₁))
      (𝓝[Ioo c' b] b) (𝓝 (lce a b f p₁ + s * (b - p₁))) :=
    (hcontg.tendsto b).mono_left nhdsWithin_le_nhds
  have hL2 : Filter.Tendsto (lce a b f) (𝓝[Ioo c' b] b)
      (𝓝 (lce a b f p₁ + s * (b - p₁))) := by
    apply hL2g.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hg_eq z hz).symm
  have hne : (𝓝[Ioo c' b] b).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt hc'b)]
    exact right_mem_Icc.mpr hc'b.le
  have hfb : f b = lce a b f p₁ + s * (b - p₁) := tendsto_nhds_unique hL1 hL2
  refine ⟨s, fun x hx => ?_⟩
  rw [hg_eq x hx]
  have : lce a b f p₁ = f b + s * (p₁ - b) := by rw [hfb]; ring
  rw [this]; ring

/-! ### `lem:two-point-convex-minorant`: the two-point representation of the convex minorant -/

/-- **Lower-bound half of `lem:two-point-convex-minorant`.**  Jensen for the convex `lce`, plus `lce ≤ f`. -/
theorem lce_le_twoPoint {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {x : ℝ} (_hx : x ∈ Icc a b) : ∀ y ∈ twoPointVals a b f x, lce a b f x ≤ y := by
  rintro y ⟨x₁, hx₁, x₂, hx₂, lam, hlam, hcomb, rfl⟩
  have hconv := (convexOn_lce hab hf).2 hx₁ hx₂ hlam.1 (by linarith [hlam.2] : (0:ℝ) ≤ 1 - lam)
    (by ring)
  simp only [smul_eq_mul] at hconv
  rw [hcomb] at hconv
  have h1 : lce a b f x₁ ≤ f x₁ := lce_le_self hab hf hx₁
  have h2 : lce a b f x₂ ≤ f x₂ := lce_le_self hab hf hx₂
  nlinarith [hconv, h1, h2, hlam.1, hlam.2]

/-- The degenerate witness `(x, x, lam = 1)`: `f x` is always a two-point value at `x`.
Used when the convex minorant already touches `f` at `x`. -/
theorem twoPoint_mem_of_touch {a b : ℝ} {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc a b) :
    f x ∈ twoPointVals a b f x :=
  ⟨x, hx, x, hx, 1, ⟨zero_le_one, le_refl 1⟩, by ring, by ring⟩

/-- The value at `x` of the chord of `f` over `[c,d]` is a two-point value at `x`
(with weight `lam = (d - x)/(d - c)`). -/
theorem twoPoint_mem_chord {a b : ℝ} {f : ℝ → ℝ} {c d x : ℝ}
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c < d) (hx : x ∈ Icc c d) :
    f c + ((f d - f c) / (d - c)) * (x - c) ∈ twoPointVals a b f x := by
  have hdc : (0:ℝ) < d - c := by linarith
  refine ⟨c, hc, d, hd, (d - x) / (d - c), ⟨by
      apply div_nonneg (by linarith [hx.2]) hdc.le, by
      rw [div_le_one hdc]; linarith [hx.1]⟩, by field_simp; ring, by field_simp; ring⟩

/-- Right-continuity of `lce` at any point of `[a,b)`: at an interior point this is
continuity of a finite convex function, at the left endpoint it is `lce_tendsto_left`
combined with `lce_left_eq`. -/
theorem lce_tendsto_right_of_mem {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {c : ℝ} (hc : c ∈ Ico a b) :
    Filter.Tendsto (lce a b f) (𝓝[Ioo c b] c) (𝓝 (lce a b f c)) := by
  rcases eq_or_lt_of_le hc.1 with hca | hca
  · subst hca
    rw [lce_left_eq hab hf]
    exact lce_tendsto_left hab hf
  · have hcIoo : c ∈ Ioo a b := ⟨hca, hc.2⟩
    have hcont : ContinuousAt (lce a b f) c :=
      (lce_continuousOn_Ioo hab.le hf).continuousAt (isOpen_Ioo.mem_nhds hcIoo)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- Left-continuity of `lce` at any point of `(a,b]` (mirror of
`lce_tendsto_right_of_mem`). -/
theorem lce_tendsto_left_of_mem {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {d : ℝ} (hd : d ∈ Ioc a b) :
    Filter.Tendsto (lce a b f) (𝓝[Ioo a d] d) (𝓝 (lce a b f d)) := by
  rcases eq_or_lt_of_le hd.2 with hdb | hdb
  · subst hdb
    rw [lce_right_eq hab hf]
    exact lce_tendsto_right hab hf
  · have hdIoo : d ∈ Ioo a b := ⟨hd.1, hdb⟩
    have hcont : ContinuousAt (lce a b f) d :=
      (lce_continuousOn_Ioo hab.le hf).continuousAt (isOpen_Ioo.mem_nhds hdIoo)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- **The chord lower bound on a detached component, with endpoints allowed at `a` or
`b`.**  This is `lce_ge_chord_on_component` with `a < c`, `d < b` weakened to `a ≤ c`,
`d ≤ b`; the variational kernel `lce_ge_chord_compact` already only needs the weak
hypotheses, so only the two endpoint limits change (they now come from
`lce_tendsto_right_of_mem` / `lce_tendsto_left_of_mem`).  The weakening is exactly what
`lem:two-point-convex-minorant` needs, since `exists_left_contact` may return `c = a` and `exists_right_contact`
may return `d = b`. -/
theorem lce_ge_chord_general {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {c d : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (hcomp : ∀ y ∈ Ioo c d, lce a b f y < f y) :
    ∀ x ∈ Icc c d,
      lce a b f c + ((lce a b f d - lce a b f c) / (d - c)) * (x - c) ≤ lce a b f x := by
  have hdcpos : (0:ℝ) < d - c := by linarith
  have hdcne : d - c ≠ 0 := ne_of_gt hdcpos
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxc | hxc
  · rw [← hxc]; simp
  rcases eq_or_lt_of_le hx.2 with hxd | hxd
  · have hval : ((lce a b f d - lce a b f c) / (d - c)) * (d - c)
        = lce a b f d - lce a b f c := by field_simp
    rw [hxd]; linarith [hval]
  have hδ : (0:ℝ) < min (x - c) (d - x) := lt_min (by linarith) (by linarith)
  set g : ℝ → ℝ := fun t => lce a b f (c + t) +
    ((lce a b f (d - t) - lce a b f (c + t)) / ((d - t) - (c + t))) * (x - (c + t)) with hg
  -- the compact-subinterval bound, for every small `t > 0`
  have hgle : ∀ᶠ t in 𝓝[>] (0:ℝ), g t ≤ lce a b f x := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    have ht0 : 0 < t := ht.1
    have htδ : t < min (x - c) (d - x) := ht.2
    have hcc' : c < c + t := by linarith
    have hc'x : c + t < x := by linarith [lt_of_lt_of_le htδ (min_le_left _ _)]
    have hxd' : x < d - t := by linarith [lt_of_lt_of_le htδ (min_le_right _ _)]
    have hd'd : d - t < d := by linarith
    exact lce_ge_chord_compact hf hcd hac hdb hcomp hcc' (lt_trans hc'x hxd') hd'd x
      ⟨hc'x.le, hxd'.le⟩
  -- the two moving endpoints converge to `c` and `d` from inside the component
  have hlc : Filter.Tendsto (fun t : ℝ => lce a b f (c + t)) (𝓝[>] (0:ℝ))
      (𝓝 (lce a b f c)) := by
    refine (lce_tendsto_right_of_mem hab hf ⟨hac, lt_of_lt_of_le hcd hdb⟩).comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous (fun t : ℝ => c + t) := by fun_prop
      simpa using (hcont.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      have ht0 : 0 < t := ht.1
      have htδ := lt_of_lt_of_le ht.2 (min_le_right (x - c) (d - x))
      exact ⟨by linarith, by linarith [hx.2]⟩
  have hld : Filter.Tendsto (fun t : ℝ => lce a b f (d - t)) (𝓝[>] (0:ℝ))
      (𝓝 (lce a b f d)) := by
    refine (lce_tendsto_left_of_mem hab hf ⟨lt_of_le_of_lt hac hcd, hdb⟩).comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous (fun t : ℝ => d - t) := by fun_prop
      simpa using (hcont.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      have ht0 : 0 < t := ht.1
      have htδ := lt_of_lt_of_le ht.2 (min_le_left (x - c) (d - x))
      exact ⟨by linarith [hx.1], by linarith⟩
  have hden : Filter.Tendsto (fun t : ℝ => (d - t) - (c + t)) (𝓝[>] (0:ℝ)) (𝓝 (d - c)) := by
    have hcont : Continuous (fun t : ℝ => (d - t) - (c + t)) := by fun_prop
    simpa using (hcont.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hxnum : Filter.Tendsto (fun t : ℝ => x - (c + t)) (𝓝[>] (0:ℝ)) (𝓝 (x - c)) := by
    have hcont : Continuous (fun t : ℝ => x - (c + t)) := by fun_prop
    simpa using (hcont.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hgtend : Filter.Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (lce a b f c +
      ((lce a b f d - lce a b f c) / (d - c)) * (x - c))) := by
    rw [hg]; exact hlc.add (((hld.sub hlc).div hden hdcne).mul hxnum)
  exact le_of_tendsto hgtend hgle

/-- **Chord identity on a detached component**, with endpoints allowed at `a` or `b`,
and stated in terms of `f` rather than `lce`.  This is the form `lem:two-point-convex-minorant` consumes. -/
theorem lce_eq_chord_general {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {c d : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (hc : lce a b f c = f c) (hd : lce a b f d = f d)
    (hcomp : ∀ y ∈ Ioo c d, lce a b f y < f y) :
    ∀ x ∈ Icc c d, lce a b f x = f c + ((f d - f c) / (d - c)) * (x - c) := by
  intro x hx
  have hle := lce_le_chord hab.le hf hcd hac hdb hx
  have hge := lce_ge_chord_general hab hf hac hcd hdb hcomp x hx
  rw [hc, hd] at hle hge
  linarith

/-- On a degenerate interval `[a,a]` the convex minorant is `f` itself. -/
theorem lce_self_of_eq {a : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a a)) :
    lce a a f a = f a := by
  have haa : a ∈ Icc a a := left_mem_Icc.mpr le_rfl
  refine le_antisymm (lce_le_self le_rfl hf haa) ?_
  have hmin : ∀ t ∈ Icc a a, (0:ℝ) * t + f a ≤ f t := by
    intro t ht
    rw [le_antisymm ht.2 ht.1]
    simp
  simpa using affine_le_lce hmin haa

/-- **`lem:two-point-convex-minorant` (two-point representation of the convex minorant).**  For a compact
interval `[a,b]` and `f` continuous on it, the value of the convex minorant at `x` is the
*minimum* — attained, hence `IsLeast` — of the two-point convex combinations of `f`
representing `x`:
`hat f (x) = min {lam * f x₁ + (1 - lam) * f x₂ : x₁, x₂ ∈ [a,b], lam ∈ [0,1],
lam * x₁ + (1 - lam) * x₂ = x}`.

The lower bound is Jensen for the convex `lce` together with `lce ≤ f`.  For attainment:
either `lce` already touches `f` at `x`, and the degenerate combination `(x, x, 1)` works,
or `x` is detached, in which case it lies in the interior and
`exists_left_contact`/`exists_right_contact` bracket it by contacts `a ≤ c < x < d ≤ b`
across which `lce` is the chord of `f` (`lce_eq_chord_general`); that chord value is the
two-point combination of `f c` and `f d`. -/
theorem lce_isLeast_twoPoint {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    IsLeast (twoPointVals a b f x) (lce a b f x) := by
  refine ⟨?_, lce_le_twoPoint hab hf hx⟩
  rcases eq_or_lt_of_le hab with hab' | hab'
  · -- degenerate interval: `x = a = b`
    subst hab'
    have hxa : x = a := le_antisymm hx.2 hx.1
    subst hxa
    rw [lce_self_of_eq hf]
    exact twoPoint_mem_of_touch hx
  rcases eq_or_lt_of_le (lce_le_self hab hf hx) with heq | hlt
  · rw [heq]; exact twoPoint_mem_of_touch hx
  · -- `x` is detached, hence interior
    have hxa : x ≠ a := by rintro rfl; rw [lce_left_eq hab' hf] at hlt; exact lt_irrefl _ hlt
    have hxb : x ≠ b := by rintro rfl; rw [lce_right_eq hab' hf] at hlt; exact lt_irrefl _ hlt
    have hxIoo : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    obtain ⟨c, hac, hcx, hfc, hleft⟩ := exists_left_contact hab' hf hxIoo hlt
    obtain ⟨d, hxd, hdb, hfd, hright⟩ := exists_right_contact hab' hf hxIoo hlt
    have hcomp : ∀ y ∈ Ioo c d, lce a b f y < f y := by
      intro y hy
      rcases lt_trichotomy y x with h | h | h
      · exact hleft y ⟨hy.1, h⟩
      · rw [h]; exact hlt
      · exact hright y ⟨h, hy.2⟩
    have hval := lce_eq_chord_general hab' hf hac (lt_trans hcx hxd) hdb hfc hfd hcomp x
      ⟨hcx.le, hxd.le⟩
    rw [hval]
    exact twoPoint_mem_chord ⟨hac, le_trans (le_trans hcx.le hxd.le) hdb⟩
      ⟨le_trans hac (le_trans hcx.le hxd.le), hdb⟩ (lt_trans hcx hxd) ⟨hcx.le, hxd.le⟩

/-- The `sInf` form of `lem:two-point-convex-minorant`. -/
theorem lce_eq_sInf_twoPoint {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    lce a b f x = sInf (twoPointVals a b f x) :=
  (lce_isLeast_twoPoint hab hf hx).csInf_eq.symm

end UpperTailOptimizers
