import UpperTailOptimizers.LZBoundary.Arc
import UpperTailOptimizers.Graphon.JpConvexity
import UpperTailOptimizers.Nondegeneracy.PowBounds

/-!
# Uniform bounds on compact subarcs, and the `u`-coordinate quadratic separation

Section 5 of `paper/bipodal_optimizer.tex` works uniformly for `r` in a compact subarc
`K ⊆ U` of a Lubetzky–Zhao boundary arc.  This file provides:

* `LZBoundaryArc.continuousOn_pc` / `continuousOn_sm` — continuity of the arc maps;
* `arc_uniform_bounds` — a single margin `η > 0` with
  `η ≤ r, sm r, pc r`, `r, sm r ≤ 1 - η` and `η ≤ |sm r - r|` for all `r ∈ K`
  (the compactness constants `η_K`, `κ` of the paper);
* `quadSep_dist` — the `u`-coordinate quadratic separation (eq. `g-r-quadratic`):
  `γ · min(|u-r|, |u-sm r|)² ≤ J_{pc r}(u) - ℓ_r(u^d)` uniformly on `K`,
  derived from the `x = u^d`-coordinate field `LZBoundaryArc.quadSep` ((M5) of `thm:scalar-lz-boundary`) via
  `|u^d - v^d| ≥ v^{d-1} |u - v|`;
* explicit box bounds for the scalar entropy: `abs_log_le_box`, `Jp_abs_le_box`,
  `Jp'_abs_le_box`, the Lipschitz bound `Jp'_lipschitz_box`, and the first-order
  Taylor bound `Jp_taylor_box` (used by the quadratic upper bound of §5.2).
-/

namespace UpperTailOptimizers

open Real Set

/-- Pointwise minimum of two `ContinuousOn` functions is `ContinuousOn`. -/
theorem continuousOn_min {f g : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun r => min (f r) (g r)) s :=
  continuous_min.comp_continuousOn (hf.prodMk hg)

/-- The boundary curve `pc` of a Lubetzky–Zhao boundary arc is continuous on the arc. -/
theorem LZBoundaryArc.continuousOn_pc {d : ℕ} (M : LZBoundaryArc d) : ContinuousOn M.pc M.U :=
  fun r hr => (M.analytic_pc r hr).continuousAt.continuousWithinAt

/-- The second-contact map `sm` of a Lubetzky–Zhao boundary arc is continuous on the arc. -/
theorem LZBoundaryArc.continuousOn_sm {d : ℕ} (M : LZBoundaryArc d) : ContinuousOn M.sm M.U :=
  fun r hr => (M.analytic_sm r hr).continuousAt.continuousWithinAt

/-- **Uniform compactness margins on a compact subarc.**  On a compact `K ⊆ U` there is a
single margin `η ∈ (0, 1/2]` with `η ≤ r ≤ 1-η`, `η ≤ sm r ≤ 1-η`, `η ≤ pc r`, and
`η ≤ |sm r - r|`, for every `r ∈ K`. -/
theorem arc_uniform_bounds {d : ℕ} (M : LZBoundaryArc d) {K : Set ℝ} (hK : K ⊆ M.U)
    (hKc : IsCompact K) (hKne : K.Nonempty) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/2 ∧ ∀ r ∈ K,
      η ≤ r ∧ r ≤ 1 - η ∧ η ≤ M.sm r ∧ M.sm r ≤ 1 - η ∧ η ≤ M.pc r ∧ η ≤ |M.sm r - r| := by
  have hsm : ContinuousOn M.sm K := M.continuousOn_sm.mono hK
  have hpc : ContinuousOn M.pc K := M.continuousOn_pc.mono hK
  -- the pointwise margin, as a single continuous function
  set g : ℝ → ℝ := fun r =>
    min (min (min r (1 - r)) (min (M.sm r) (1 - M.sm r))) (min (M.pc r) |M.sm r - r|) with hg
  have hgc : ContinuousOn g K := by
    refine continuousOn_min (continuousOn_min (continuousOn_min continuousOn_id ?_)
      (continuousOn_min hsm ?_)) (continuousOn_min hpc ?_)
    · exact (continuous_const.sub continuous_id).continuousOn
    · exact continuousOn_const.sub hsm
    · exact (hsm.sub continuousOn_id).abs
  have hgpos : ∀ r ∈ K, 0 < g r := by
    intro r hr
    obtain ⟨hpc0, hpcr, hr1, hsmne, hsm0, hsm1⟩ := M.ordering r (hK hr)
    have hr0 : 0 < r := lt_trans hpc0 hpcr
    have habs : 0 < |M.sm r - r| := abs_pos.mpr (sub_ne_zero.mpr hsmne)
    have h1 : (0:ℝ) < 1 - r := by linarith
    have h2 : (0:ℝ) < 1 - M.sm r := by linarith
    simp only [hg, lt_min_iff]
    exact ⟨⟨⟨hr0, h1⟩, ⟨hsm0, h2⟩⟩, ⟨hpc0, habs⟩⟩
  obtain ⟨r₀, hr₀K, hmin⟩ := hKc.exists_isMinOn hKne hgc
  rw [isMinOn_iff] at hmin
  refine ⟨min (1/2) (g r₀), lt_min (by norm_num) (hgpos r₀ hr₀K), min_le_left _ _, ?_⟩
  intro r hr
  have hle : min (1/2) (g r₀) ≤ g r := le_trans (min_le_right _ _) (hmin r hr)
  have h1 : g r ≤ r := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have h2 : g r ≤ 1 - r :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have h3 : g r ≤ M.sm r :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h4 : g r ≤ 1 - M.sm r :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h5 : g r ≤ M.pc r := le_trans (min_le_right _ _) (min_le_left _ _)
  have h6 : g r ≤ |M.sm r - r| := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨le_trans hle h1, ?_, le_trans hle h3, ?_, le_trans hle h5, le_trans hle h6⟩
  · linarith [le_trans hle h2]
  · linarith [le_trans hle h4]

/-- **`u`-coordinate quadratic separation** (eq. `g-r-quadratic` of the paper).  On a compact
subarc `K` there is `γ > 0`, uniform over `r ∈ K` and `u ∈ [0,1]`, with
`γ · min(|u - r|, |u - sm r|)² ≤ J_{pc r}(u) - (J_{pc r}(r) + slope·(u^d - r^d))`.
Derived from the `x`-coordinate field `LZBoundaryArc.quadSep` ((M5) of `thm:scalar-lz-boundary`) via
`|u^d - v^d| ≥ v^{d-1}|u - v|`. -/
theorem quadSep_dist {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {K : Set ℝ} (hK : K ⊆ M.U)
    (hKc : IsCompact K) (hKne : K.Nonempty) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ r ∈ K, ∀ u ∈ Set.Icc (0:ℝ) 1,
      γ * (min |u - r| |u - M.sm r|) ^ 2
        ≤ Jp (M.pc r) u - (Jp (M.pc r) r + slope d M.pc r * (u ^ d - r ^ d)) := by
  obtain ⟨γ₀, hγ₀, hsep⟩ := M.quadSep K hK hKc
  obtain ⟨η, hη0, _, hηbd⟩ := arc_uniform_bounds M hK hKc hKne
  refine ⟨γ₀ * (η ^ (d - 1)) ^ 2, by positivity, ?_⟩
  intro r hr u hu
  obtain ⟨hηr, hr1, hηs, hs1, _, _⟩ := hηbd r hr
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  -- `|u^d - v^d| ≥ η^{d-1} |u - v|` for the two contact points `v = r, sm r`
  have hkey : ∀ v : ℝ, η ≤ v → η ^ (d - 1) * |u - v| ≤ |u ^ d - v ^ d| := by
    intro v hv
    have hv0 : 0 ≤ v := le_trans hη0.le hv
    calc η ^ (d - 1) * |u - v| ≤ v ^ (d - 1) * |u - v| :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hη0.le hv _) (abs_nonneg _)
      _ ≤ |u ^ d - v ^ d| := pow_sub_pow_ge hu.1 hv0 hd1
  -- pass to the minimum over the two contacts
  have hmin : η ^ (d - 1) * min |u - r| |u - M.sm r|
      ≤ min |u ^ d - r ^ d| |u ^ d - (M.sm r) ^ d| := by
    refine le_min ?_ ?_
    · exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)) (hkey r hηr)
    · exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))
        (hkey (M.sm r) hηs)
  -- square and chain with the `x`-coordinate separation `LZBoundaryArc.quadSep`
  have hminnn : 0 ≤ η ^ (d - 1) * min |u - r| |u - M.sm r| := by
    have : (0:ℝ) ≤ min |u - r| |u - M.sm r| := le_min (abs_nonneg _) (abs_nonneg _)
    positivity
  have hsq : (η ^ (d - 1) * min |u - r| |u - M.sm r|) ^ 2
      ≤ (min |u ^ d - r ^ d| |u ^ d - (M.sm r) ^ d|) ^ 2 :=
    pow_le_pow_left₀ hminnn hmin 2
  calc γ₀ * (η ^ (d - 1)) ^ 2 * (min |u - r| |u - M.sm r|) ^ 2
      = γ₀ * (η ^ (d - 1) * min |u - r| |u - M.sm r|) ^ 2 := by ring
    _ ≤ γ₀ * (min |u ^ d - r ^ d| |u ^ d - (M.sm r) ^ d|) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hγ₀.le
    _ ≤ Jp (M.pc r) u - (Jp (M.pc r) r + slope d M.pc r * (u ^ d - r ^ d)) := hsep r hr u hu

/-! ### Explicit box bounds for `Jp`, `Jp'`, and the first-order Taylor remainder. -/

/-- `|log x| ≤ -log β` for `β ≤ x ≤ 1`, `β > 0`. -/
theorem abs_log_le_box {β x : ℝ} (hβ : 0 < β) (hx : β ≤ x) (hx1 : x ≤ 1) :
    |Real.log x| ≤ -Real.log β := by
  have hx0 : 0 < x := lt_of_lt_of_le hβ hx
  rw [abs_of_nonpos (Real.log_nonpos hx0.le hx1)]
  have := Real.log_le_log hβ hx
  linarith

/-- Uniform bound for `Jp` on the box `p, u ∈ [β, 1-β]`: `|J_p(u)| ≤ 2·(-log β)`. -/
theorem Jp_abs_le_box {β p u : ℝ} (hβ : 0 < β) (hp : p ∈ Set.Icc β (1 - β))
    (hu : u ∈ Set.Icc β (1 - β)) : |Jp p u| ≤ 2 * (-Real.log β) := by
  have hβ1 : β < 1 := by
    have : β ≤ 1 - β := le_trans hp.1 hp.2
    linarith
  have hp0 : 0 < p := lt_of_lt_of_le hβ hp.1
  have hu0 : 0 < u := lt_of_lt_of_le hβ hu.1
  have hp1 : p ≤ 1 := by linarith [hp.2]
  have hu1 : u ≤ 1 := by linarith [hu.2]
  have h1p : β ≤ 1 - p := by linarith [hp.2]
  have h1u : β ≤ 1 - u := by linarith [hu.2]
  have h1p1 : 1 - p ≤ 1 := by linarith [hp.1]
  have h1u1 : 1 - u ≤ 1 := by linarith [hu.1]
  have h1p0 : (0:ℝ) < 1 - p := lt_of_lt_of_le hβ h1p
  have h1u0 : (0:ℝ) ≤ 1 - u := le_trans hβ.le h1u
  -- bound each log difference by `2·(-log β)`
  have hlog1 : |Real.log (u / p)| ≤ 2 * (-Real.log β) := by
    rw [Real.log_div (ne_of_gt hu0) (ne_of_gt hp0)]
    calc |Real.log u - Real.log p| ≤ |Real.log u| + |Real.log p| := abs_sub _ _
      _ ≤ (-Real.log β) + (-Real.log β) :=
          add_le_add (abs_log_le_box hβ hu.1 hu1) (abs_log_le_box hβ hp.1 hp1)
      _ = 2 * (-Real.log β) := by ring
  have hlog2 : |Real.log ((1 - u) / (1 - p))| ≤ 2 * (-Real.log β) := by
    rw [Real.log_div (by linarith : (1:ℝ) - u ≠ 0) (ne_of_gt h1p0)]
    calc |Real.log (1 - u) - Real.log (1 - p)| ≤ |Real.log (1 - u)| + |Real.log (1 - p)| :=
          abs_sub _ _
      _ ≤ (-Real.log β) + (-Real.log β) :=
          add_le_add (abs_log_le_box hβ h1u h1u1) (abs_log_le_box hβ h1p h1p1)
      _ = 2 * (-Real.log β) := by ring
  have hβlog : 0 ≤ -Real.log β := by
    have := Real.log_nonpos hβ.le hβ1.le
    linarith
  calc |Jp p u| = |u * Real.log (u / p) + (1 - u) * Real.log ((1 - u) / (1 - p))| := rfl
    _ ≤ |u * Real.log (u / p)| + |(1 - u) * Real.log ((1 - u) / (1 - p))| := abs_add_le _ _
    _ = u * |Real.log (u / p)| + (1 - u) * |Real.log ((1 - u) / (1 - p))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hu0.le, abs_of_nonneg h1u0]
    _ ≤ u * (2 * (-Real.log β)) + (1 - u) * (2 * (-Real.log β)) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog1 hu0.le)
          (mul_le_mul_of_nonneg_left hlog2 h1u0)
    _ = 2 * (-Real.log β) := by ring

/-- Uniform bound for `Jp'` on the box `p, u ∈ [β, 1-β]`: `|J_p'(u)| ≤ 4·(-log β)`. -/
theorem Jp'_abs_le_box {β p u : ℝ} (hβ : 0 < β) (hp : p ∈ Set.Icc β (1 - β))
    (hu : u ∈ Set.Icc β (1 - β)) : |Jp' p u| ≤ 4 * (-Real.log β) := by
  have hp0 : 0 < p := lt_of_lt_of_le hβ hp.1
  have hu0 : 0 < u := lt_of_lt_of_le hβ hu.1
  have hp1 : p ≤ 1 := by nlinarith [hp.2, hp.1]
  have hu1 : u ≤ 1 := by nlinarith [hu.2, hu.1]
  have h1p : β ≤ 1 - p := by linarith [hp.2]
  have h1u : β ≤ 1 - u := by linarith [hu.2]
  have h1p1 : 1 - p ≤ 1 := by linarith [hp.1]
  have h1u1 : 1 - u ≤ 1 := by linarith [hu.1]
  have h1p0 : (0:ℝ) < 1 - p := lt_of_lt_of_le hβ h1p
  have h1u0 : (0:ℝ) < 1 - u := lt_of_lt_of_le hβ h1u
  have hexp : Jp' p u = Real.log u + Real.log (1 - p) - (Real.log (1 - u) + Real.log p) := by
    unfold Jp'
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (ne_of_gt hu0) (ne_of_gt h1p0),
      Real.log_mul (ne_of_gt h1u0) (ne_of_gt hp0)]
  rw [hexp]
  have b1 := abs_log_le_box hβ hu.1 hu1
  have b2 := abs_log_le_box hβ h1p h1p1
  have b3 := abs_log_le_box hβ h1u h1u1
  have b4 := abs_log_le_box hβ hp.1 hp1
  calc |Real.log u + Real.log (1 - p) - (Real.log (1 - u) + Real.log p)|
      ≤ |Real.log u + Real.log (1 - p)| + |Real.log (1 - u) + Real.log p| := abs_sub _ _
    _ ≤ (|Real.log u| + |Real.log (1 - p)|) + (|Real.log (1 - u)| + |Real.log p|) :=
        add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ ≤ ((-Real.log β) + (-Real.log β)) + ((-Real.log β) + (-Real.log β)) :=
        add_le_add (add_le_add b1 b2) (add_le_add b3 b4)
    _ = 4 * (-Real.log β) := by ring

/-- `t(1-t)` is minimised at the endpoints of `[β, 1-β]`: `β(1-β) ≤ t(1-t)`. -/
theorem mul_one_sub_ge_box {β t : ℝ} (ht : t ∈ Set.Icc β (1 - β)) :
    β * (1 - β) ≤ t * (1 - t) := by
  nlinarith [ht.1, ht.2]

/-- **Lipschitz bound for `Jp'`** on the box `u ∈ [β, 1-β]` (from `Jp'' ≤ 1/(β(1-β))`):
`|J_p'(x) - J_p'(y)| ≤ (1/(β(1-β)))·|x - y|`. -/
theorem Jp'_lipschitz_box {β p x y : ℝ} (hβ : 0 < β) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Set.Icc β (1 - β)) (hy : y ∈ Set.Icc β (1 - β)) :
    |Jp' p x - Jp' p y| ≤ (1 / (β * (1 - β))) * |x - y| := by
  have hβ1 : β < 1 := by
    have : β ≤ 1 - β := le_trans hx.1 hx.2
    linarith
  have hderiv : ∀ t ∈ Set.Icc β (1 - β),
      HasDerivWithinAt (Jp' p) (Jp'' t) (Set.Icc β (1 - β)) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hβ ht.1
    have ht1 : t < 1 := by
      have : t ≤ 1 - β := ht.2
      linarith
    exact (hasDerivAt_Jp' hp0 hp1 ht0 ht1).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc β (1 - β), ‖Jp'' t‖ ≤ 1 / (β * (1 - β)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hβ ht.1
    have ht1 : t < 1 := by
      have : t ≤ 1 - β := ht.2
      linarith
    have hpos : 0 < t * (1 - t) := by nlinarith
    have hβpos : 0 < β * (1 - β) := by nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Jp''_pos ht0 ht1).le]
    unfold Jp''
    exact one_div_le_one_div_of_le hβpos (mul_one_sub_ge_box ht)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc β (1 - β)) hy hx
  simpa [Real.norm_eq_abs] using this

/-- Points of the unordered interval `[x ⊓ y, x ⊔ y]` are within `|x - y|` of `y`. -/
theorem abs_sub_le_of_mem_uIcc {x y t : ℝ} (ht : t ∈ Set.uIcc x y) : |t - y| ≤ |x - y| := by
  have h1 : x - y ≤ |x - y| := le_abs_self _
  have h2 : y - x ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
  rcases Set.mem_uIcc.mp ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [abs_sub_le_iff] <;>
    constructor <;> linarith

/-- **First-order Taylor bound for `Jp`** on the box `x, y ∈ [β, 1-β]`:
`|J_p(x) - J_p(y) - J_p'(y)(x - y)| ≤ (1/(β(1-β)))·(x-y)²`. -/
theorem Jp_taylor_box {β p x y : ℝ} (hβ : 0 < β) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Set.Icc β (1 - β)) (hy : y ∈ Set.Icc β (1 - β)) :
    |Jp p x - Jp p y - Jp' p y * (x - y)| ≤ (1 / (β * (1 - β))) * (x - y) ^ 2 := by
  have hsub : Set.uIcc x y ⊆ Set.Icc β (1 - β) := Set.uIcc_subset_Icc hx hy
  -- the auxiliary function `g t = Jp p t - Jp' p y · t` has derivative `Jp' p t - Jp' p y`
  have hderiv : ∀ t ∈ Set.uIcc x y,
      HasDerivWithinAt (fun t => Jp p t - Jp' p y * t) (Jp' p t - Jp' p y) (Set.uIcc x y) t := by
    intro t ht
    have htbox := hsub ht
    have ht0 : 0 < t := lt_of_lt_of_le hβ htbox.1
    have ht1 : t < 1 := by
      have hβ1 : β ≤ 1 - β := le_trans hx.1 hx.2
      have : t ≤ 1 - β := htbox.2
      linarith
    have h1 : HasDerivAt (Jp p) (Jp' p t) t := hasDerivAt_Jp hp0 hp1 ht0 ht1
    have h2 : HasDerivAt (fun t : ℝ => Jp' p y * t) (Jp' p y) t := by
      simpa using (hasDerivAt_id t).const_mul (Jp' p y)
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc x y,
      ‖Jp' p t - Jp' p y‖ ≤ (1 / (β * (1 - β))) * |x - y| := by
    intro t ht
    rw [Real.norm_eq_abs]
    calc |Jp' p t - Jp' p y| ≤ (1 / (β * (1 - β))) * |t - y| :=
          Jp'_lipschitz_box hβ hp0 hp1 (hsub ht) hy
      _ ≤ (1 / (β * (1 - β))) * |x - y| := by
          have hβ1 : β ≤ 1 - β := le_trans hx.1 hx.2
          have hpos : (0:ℝ) ≤ 1 / (β * (1 - β)) := by
            have : 0 < β * (1 - β) := by nlinarith
            positivity
          exact mul_le_mul_of_nonneg_left (abs_sub_le_of_mem_uIcc ht) hpos
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc x y) Set.right_mem_uIcc Set.left_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hexp : (Jp p x - Jp' p y * x) - (Jp p y - Jp' p y * y)
      = Jp p x - Jp p y - Jp' p y * (x - y) := by ring
  rw [hexp] at hmvt
  calc |Jp p x - Jp p y - Jp' p y * (x - y)|
      ≤ (1 / (β * (1 - β))) * |x - y| * |x - y| := hmvt
    _ = (1 / (β * (1 - β))) * (x - y) ^ 2 := by
        rw [mul_assoc, ← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]

end UpperTailOptimizers
