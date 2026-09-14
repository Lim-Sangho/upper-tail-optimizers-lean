import UpperTailOptimizers.NonexceptionalEndpoint.Proof.Basic

/-!
# The tilted scalar problem of Section 4.3

Section 4.3 of `paper/paper.tex` reduces the upper-tail problem, on the symmetry-breaking side, to minimising

`δ ↦ G_r(δ) - λ(p,r)·δ`   over `δ ∈ (0, δ₀)`

(`eq:edge-deficit-minimization`), where `G_r` is the boundary excess of Section 4.2.  This
file isolates the one-variable analysis, stated for an abstract `C²` function `g` with
`g'(0) = 0` and `g'' ≥ a > 0` on a two-sided interval — exactly the data the analytic chart
`boundaryExcess_chart` supplies.

`tilted_critical_point` produces the critical point `δ_*` and proves everything Section 4.3
needs about it in one go: existence, the equation `g'(δ_*) = λ`, the bound `δ_* ≤ λ/a`, that
`δ_*` is the **unique** minimiser of the tilted objective on `(0, δ₀)`, and the first-order
expansion `|λ - A δ_*| ≤ Mc δ_*²` coming from `|g''(t) - A| ≤ Mc |t|`.

Deviation from the paper: the paper locates the critical point with the analytic implicit
function theorem at `(pc(r₀), r₀, 0)`, then bounds it by the mean value theorem and obtains
uniqueness from strict convexity.  Here it is located by the
intermediate value theorem against the strictly increasing `g'`, which is *quantitative*
(the admissible range `0 < λ < a δ₀` is explicit) and makes the sign and
size of `δ_*` immediate.  The implicit function theorem is still used, but only for the
analyticity assertion of `thm:nonexceptional-endpoint`.
-/

namespace UpperTailOptimizers

open Set

/-- **Strict monotonicity from a positive derivative** on a closed interval (mean value
theorem form). -/
theorem strictMonoOn_of_hasDerivAt_pos {f f' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Icc a b, 0 < f' t) : StrictMonoOn f (Icc a b) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hcont : ContinuousOn f (Icc x y) :=
    fun t ht => ((hd t (hsub ht)).continuousAt).continuousWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope f f' hxy hcont
    (fun t ht => hd t (hsub (Ioo_subset_Icc_self ht)))
  have hcpos : 0 < f' c := hpos c (hsub (Ioo_subset_Icc_self hc))
  rw [hceq] at hcpos
  have hyx : 0 < y - x := by linarith
  by_contra hcon
  push Not at hcon
  have : (f y - f x) / (y - x) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hyx.le
  linarith

/-- **The tilted scalar problem.**  Let `g` be twice differentiable on `[-δ₀, δ₀]`, with
derivatives `g1`, `g2`, and suppose

* `g1 0 = 0` (the boundary is a critical point of the untilted objective),
* `a ≤ g2` on `[-δ₀, δ₀]` with `a > 0` (uniform strict convexity),
* `|g2 t - A| ≤ Mc |t|` (the second derivative is `Mc`-Lipschitz around its value `A` at `0`).

Then for every tilt `0 < λ < a δ₀` there is a `δ_* ∈ (0, δ₀)` with

* `g1 δ_* = λ` and `δ_* ≤ λ / a`;
* `δ_*` is the **unique** minimiser of `δ ↦ g δ - λ δ` on `(0, δ₀)`;
* `|λ - A δ_*| ≤ Mc δ_*²`, the first-order expansion of the critical point;
* `δ_*` is the **unique root** of `g' = λ` on the whole two-sided interval `[-δ₀, δ₀]`
  (immediate from strict monotonicity of `g'`).  This last clause is what identifies the
  analytic implicit-function family of Section 4.3 with `δ_*`: that family is only known to
  solve the critical-point equation, and a priori only known to lie *near* `0`, so
  minimiser-uniqueness on `(0, δ₀)` cannot reach it.
-/
theorem tilted_critical_point {g g1 g2 : ℝ → ℝ} {δ₀ a A Mc lam : ℝ}
    (hδ₀ : 0 < δ₀) (ha : 0 < a)
    (hd1 : ∀ t ∈ Icc (-δ₀) δ₀, HasDerivAt g (g1 t) t)
    (hd2 : ∀ t ∈ Icc (-δ₀) δ₀, HasDerivAt g1 (g2 t) t)
    (hg10 : g1 0 = 0)
    (hg2 : ∀ t ∈ Icc (-δ₀) δ₀, a ≤ g2 t)
    (hg2A : ∀ t ∈ Icc (-δ₀) δ₀, |g2 t - A| ≤ Mc * |t|)
    (hlam0 : 0 < lam) (hlam : lam < a * δ₀) :
    ∃ ds ∈ Ioo (0:ℝ) δ₀, g1 ds = lam ∧ ds ≤ lam / a ∧
      (∀ δ ∈ Ioo (0:ℝ) δ₀, δ ≠ ds → g ds - lam * ds < g δ - lam * δ) ∧
      |lam - A * ds| ≤ Mc * ds ^ 2 ∧
      (∀ t ∈ Icc (-δ₀) δ₀, g1 t = lam → t = ds) := by
  have h0mem : (0:ℝ) ∈ Icc (-δ₀) δ₀ := ⟨by linarith, hδ₀.le⟩
  have hδ₀mem : δ₀ ∈ Icc (-δ₀) δ₀ := ⟨by linarith, le_rfl⟩
  -- `g1` is strictly increasing on the whole two-sided interval
  have hmono : StrictMonoOn g1 (Icc (-δ₀) δ₀) :=
    strictMonoOn_of_hasDerivAt_pos hd2 (fun t ht => lt_of_lt_of_le ha (hg2 t ht))
  -- `g1 δ ≥ a δ` on `[0, δ₀]`
  have hlow : ∀ δ ∈ Icc (0:ℝ) δ₀, a * δ ≤ g1 δ := by
    intro δ hδ
    rcases eq_or_lt_of_le hδ.1 with h | h
    · rw [← h, hg10]; simp
    · have hsub : Icc (0:ℝ) δ ⊆ Icc (-δ₀) δ₀ := Icc_subset_Icc (by linarith) hδ.2
      have hcont : ContinuousOn g1 (Icc 0 δ) :=
        fun t ht => ((hd2 t (hsub ht)).continuousAt).continuousWithinAt
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g1 g2 h hcont
        (fun t ht => hd2 t (hsub (Ioo_subset_Icc_self ht)))
      have hac := hg2 c (hsub (Ioo_subset_Icc_self hc))
      rw [hceq, hg10, sub_zero, sub_zero, le_div_iff₀ h] at hac
      linarith
  -- existence, by the intermediate value theorem
  have hcont01 : ContinuousOn g1 (Icc 0 δ₀) := by
    intro t ht
    exact ((hd2 t (Icc_subset_Icc (by linarith) le_rfl ht)).continuousAt).continuousWithinAt
  have hmemIoo : lam ∈ Ioo (g1 0) (g1 δ₀) := by
    refine ⟨by rw [hg10]; exact hlam0, ?_⟩
    have := hlow δ₀ ⟨hδ₀.le, le_rfl⟩
    linarith
  obtain ⟨ds, hds, hdseq⟩ := intermediate_value_Ioo hδ₀.le hcont01 hmemIoo
  have hdsmem : ds ∈ Icc (-δ₀) δ₀ := ⟨by linarith [hds.1], hds.2.le⟩
  refine ⟨ds, hds, hdseq, ?_, ?_, ?_, ?_⟩
  · -- `ds ≤ lam / a`
    have := hlow ds ⟨hds.1.le, hds.2.le⟩
    rw [hdseq] at this
    rw [le_div_iff₀ ha]
    linarith
  · -- `ds` is the unique minimiser of the tilted objective on `(0, δ₀)`
    intro δ hδ hne
    have hδmem : δ ∈ Icc (-δ₀) δ₀ := ⟨by linarith [hδ.1], hδ.2.le⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `δ < ds`: the tilted derivative is negative on `(δ, ds)`
      have hsub : Icc δ ds ⊆ Icc (-δ₀) δ₀ := Icc_subset_Icc hδmem.1 hdsmem.2
      have hcont : ContinuousOn (fun t => g t - lam * t) (Icc δ ds) := by
        intro t ht
        exact (((hd1 t (hsub ht)).sub ((hasDerivAt_id t).const_mul lam)).continuousAt
          ).continuousWithinAt
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun t => g t - lam * t)
        (fun t => g1 t - lam) hlt hcont (fun t ht => by
          have h := (hd1 t (hsub (Ioo_subset_Icc_self ht))).fun_sub
            ((hasDerivAt_id t).const_mul lam)
          simpa using h)
      have hcmem : c ∈ Icc (-δ₀) δ₀ := hsub (Ioo_subset_Icc_self hc)
      have hclt : g1 c < lam := by
        rw [← hdseq]
        exact hmono hcmem hdsmem hc.2
      have hpos : 0 < ds - δ := by linarith
      by_contra hcon
      push Not at hcon
      have hnn : 0 ≤ (g ds - lam * ds - (g δ - lam * δ)) / (ds - δ) :=
        div_nonneg (by linarith) hpos.le
      rw [← hceq] at hnn
      linarith
    · -- `δ > ds`: the tilted derivative is positive on `(ds, δ)`
      have hsub : Icc ds δ ⊆ Icc (-δ₀) δ₀ := Icc_subset_Icc hdsmem.1 hδmem.2
      have hcont : ContinuousOn (fun t => g t - lam * t) (Icc ds δ) := by
        intro t ht
        exact (((hd1 t (hsub ht)).sub ((hasDerivAt_id t).const_mul lam)).continuousAt
          ).continuousWithinAt
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun t => g t - lam * t)
        (fun t => g1 t - lam) hgt hcont (fun t ht => by
          have h := (hd1 t (hsub (Ioo_subset_Icc_self ht))).fun_sub
            ((hasDerivAt_id t).const_mul lam)
          simpa using h)
      have hcmem : c ∈ Icc (-δ₀) δ₀ := hsub (Ioo_subset_Icc_self hc)
      have hcgt : lam < g1 c := by
        rw [← hdseq]
        exact hmono hdsmem hcmem hc.1
      have hpos : 0 < δ - ds := by linarith
      by_contra hcon
      push Not at hcon
      have hnp : (g δ - lam * δ - (g ds - lam * ds)) / (δ - ds) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
      rw [← hceq] at hnp
      linarith
  · -- the first-order expansion `|lam - A ds| ≤ Mc ds²`
    have hsub : Icc (0:ℝ) ds ⊆ Icc (-δ₀) δ₀ := Icc_subset_Icc (by linarith) hds.2.le
    have hcont : ContinuousOn g1 (Icc 0 ds) :=
      fun t ht => ((hd2 t (hsub ht)).continuousAt).continuousWithinAt
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g1 g2 hds.1 hcont
      (fun t ht => hd2 t (hsub (Ioo_subset_Icc_self ht)))
    rw [hdseq, hg10, sub_zero, sub_zero] at hceq
    have hdsne : ds ≠ 0 := ne_of_gt hds.1
    have hclam : lam = g2 c * ds := by
      rw [hceq]; field_simp
    have hbound := hg2A c (hsub (Ioo_subset_Icc_self hc))
    rw [abs_of_nonneg hc.1.le] at hbound
    have hkey : |lam - A * ds| = |g2 c - A| * ds := by
      have hfac : lam - A * ds = (g2 c - A) * ds := by rw [hclam]; ring
      rw [hfac, abs_mul, abs_of_pos hds.1]
    rw [hkey]
    calc |g2 c - A| * ds ≤ (Mc * c) * ds := by
          exact mul_le_mul_of_nonneg_right hbound hds.1.le
      _ ≤ (Mc * ds) * ds := by
          have hMc0 : 0 ≤ Mc := by
            by_contra h
            push Not at h
            have : Mc * c < 0 := mul_neg_of_neg_of_pos h hc.1
            have := le_trans (abs_nonneg (g2 c - A)) hbound
            linarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hc.2.le hMc0) hds.1.le
      _ = Mc * ds ^ 2 := by ring
  · -- `ds` is the unique root of `g1 = lam` on the two-sided interval
    intro t ht hteq
    exact hmono.injOn ht hdsmem (by rw [hteq, hdseq])

end UpperTailOptimizers
