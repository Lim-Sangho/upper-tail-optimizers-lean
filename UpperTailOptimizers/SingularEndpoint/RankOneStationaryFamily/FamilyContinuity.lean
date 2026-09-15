import UpperTailOptimizers.SingularEndpoint.ConstantGraphonComparison.CostGap
import UpperTailOptimizers.LZBoundary.Curve

/-!
# Analyticity and convergence of the singular endpoint family

Every scalar attached to a `KKTFamily d` is continuous at `h = 0`, for the trivial
reason that the four primitive fields `u, p, γ, α` are analytic on the window and `0` lies
in it.  This file is the single home for those facts, together with the three entropy
compositions that everything downstream actually consumes:

* `ell_p_continuousAt` — `h ↦ ℓ(p_h)`, using `p_0 = p_* ∈ (0,1)`;
* `Jp_p_zero_continuousAt` — `h ↦ J_{p_h}(0) = -log(1 - p_h)`;
* `Jp_comp_continuousAt` — `h ↦ J_{p_h}(g h)` for a continuous `g` with `g 0 ∈ (0,1)`.
  Both the parameter and the argument move, so this goes through the exact displacement
  `eq:entropy-parameter-shift`: near `0` the function equals `J_{p_*}(g h) + Λ_h·g h + C_h`, each
  summand of which is visibly continuous.

The last is the workhorse: `κ_h`, the insertion drift and the `Ψ`-drift are all built from
`J_{p_h}` evaluated at a moving node.

## Why this file exists

`SingularEndpoint/AuxiliaryLagrangian/PsiTilde.lean` and `SingularEndpoint/AuxiliaryLagrangian/TailScalar.lean` each used to carry a private copy of
this block, because neither imports the other.  Keeping copies in step is exactly the trap
a single home avoids, so the block lives here — below both, above nothing that
needs it — and is public.

`SingularEndpoint/ConstantGraphonComparison/CostGap.lean` is the lowest file that has everything: `η_h` and `κ_h` come from
`SingularEndpoint/AuxiliaryLagrangian/FirstVariation.lean`, `s_0 = t_0 = u_*` from `CostGap.lean` itself, and the
displacement identity from `SingularEndpoint/ConstantGraphonComparison/Identities.lean`.

## Contents

* `zero_mem_window` — `|0| < h₀`, the ubiquitous side condition;
* `u_continuousAt`, `p_continuousAt`, `gam_continuousAt`, `alph_continuousAt` — the four
  primitive fields;
* `sVal_continuousAt`, `tVal_continuousAt`, `qVal_continuousAt`, `etaVal_continuousAt`,
  `kappaVal_continuousAt` — the derived scalars;
* `tendsto_p`, `tendsto_u_nhds`, `tendsto_gam_nhds` — the same facts as limits, with the
  value at `0` substituted.
* `analyticAt_qVal`, `analyticAt_rVal`, `tendsto_p_pcGlobal` — the analytic parameter curve
  and its limit on the phase boundary;
* `graphon_rankOne`, `graphon_isBipodal`, `exists_graphon_unif` — structural properties
  and uniform convergence used in Theorem 5.1 and hence its introduction corollary.
-/

namespace UpperTailOptimizers

namespace KKTFamily

open Filter Topology

variable {d : ℕ}

/-! ## The window contains `0` -/

/-- `0` lies in the family window.  Stated as `|0| < h₀` rather than `0 < h₀` because every
field of `KKTFamily` is guarded by `|h| < h₀`. -/
theorem zero_mem_window (B : KKTFamily d) : |(0 : ℝ)| < B.h₀ := by
  rw [abs_zero]
  exact B.h₀_pos

/-- The window is a neighbourhood of `0`. -/
theorem eventually_mem_window (B : KKTFamily d) : ∀ᶠ h : ℝ in 𝓝 0, |h| < B.h₀ := by
  have hb : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), h ∈ Metric.ball (0 : ℝ) B.h₀ :=
    Metric.ball_mem_nhds 0 B.h₀_pos
  filter_upwards [hb] with h hh
  simpa [Real.dist_eq] using hh

/-! ## The four primitive fields -/

theorem u_continuousAt (B : KKTFamily d) : ContinuousAt B.u 0 :=
  (B.analyticAt_u 0 (zero_mem_window B)).continuousAt

theorem p_continuousAt (B : KKTFamily d) : ContinuousAt B.p 0 :=
  (B.analyticAt_p 0 (zero_mem_window B)).continuousAt

theorem gam_continuousAt (B : KKTFamily d) : ContinuousAt B.gam 0 :=
  (B.analyticAt_gam 0 (zero_mem_window B)).continuousAt

theorem alph_continuousAt (B : KKTFamily d) : ContinuousAt B.alph 0 :=
  (B.analyticAt_alph 0 (zero_mem_window B)).continuousAt

/-! ## The derived scalars -/

theorem sVal_continuousAt (B : KKTFamily d) : ContinuousAt B.sVal 0 := by
  have h : ContinuousAt (fun h : ℝ => B.u h - h) 0 := (u_continuousAt B).sub continuousAt_id
  exact h

theorem tVal_continuousAt (B : KKTFamily d) : ContinuousAt B.tVal 0 := by
  have h : ContinuousAt (fun h : ℝ => B.u h + h) 0 := (u_continuousAt B).add continuousAt_id
  exact h

theorem qVal_continuousAt (B : KKTFamily d) : ContinuousAt B.qVal 0 := by
  have h : ContinuousAt
      (fun h : ℝ => B.alph h * B.sVal h ^ d + (1 - B.alph h) * B.tVal h ^ d) 0 :=
    ((alph_continuousAt B).mul ((sVal_continuousAt B).pow d)).add
      ((continuousAt_const.sub (alph_continuousAt B)).mul ((tVal_continuousAt B).pow d))
  exact h

theorem etaVal_continuousAt (B : KKTFamily d) : ContinuousAt B.etaVal 0 := by
  have h : ContinuousAt (fun h : ℝ => 2 * B.gam h * B.qVal h / (d : ℝ)) 0 :=
    ((continuousAt_const.mul (gam_continuousAt B)).mul (qVal_continuousAt B)).div_const _
  exact h

/-! ## The entropy compositions -/

/-- `h ↦ ℓ(p_h)` is continuous at `0`, since `p_0 = p_* ∈ (0,1)`. -/
theorem ell_p_continuousAt (hd : 2 ≤ d) (B : KKTFamily d) :
    ContinuousAt (fun h => ell (B.p h)) 0 := by
  have hp0 : 0 < pStar d := pStar_pos hd
  have hp1 : pStar d < 1 := pStar_lt_one hd
  have hell : ContinuousAt ell (pStar d) := by
    have hdiv : ContinuousAt (fun z : ℝ => (1 - z) / z) (pStar d) :=
      (continuousAt_const.sub continuousAt_id).div continuousAt_id (ne_of_gt hp0)
    exact hdiv.log (div_pos (by linarith) hp0).ne'
  rw [← B.p_zero] at hell
  have h := hell.comp (p_continuousAt B)
  exact h

/-- `h ↦ J_{p_h}(0) = -log(1 - p_h)` is continuous at `0`. -/
theorem Jp_p_zero_continuousAt (hd : 2 ≤ d) (B : KKTFamily d) :
    ContinuousAt (fun h => Jp (B.p h) 0) 0 := by
  have hp1 : pStar d < 1 := pStar_lt_one hd
  simp only [Jp_zero]
  refine ContinuousAt.neg (ContinuousAt.log (continuousAt_const.sub (p_continuousAt B)) ?_)
  rw [B.p_zero]
  exact ne_of_gt (show (0 : ℝ) < 1 - pStar d by linarith)

/-- **Continuity of `h ↦ J_{p_h}(g h)`** at `0`, for a continuous `g` with `g 0 ∈ (0,1)`.

Both the parameter and the argument move, so this goes through the exact displacement
`eq:entropy-parameter-shift`: near `0` the function equals `J_{p_*}(g h) + Λ_h·g h + C_h`, each
summand of which is visibly continuous. -/
theorem Jp_comp_continuousAt (hd : 2 ≤ d) (B : KKTFamily d) {g : ℝ → ℝ}
    (hg : ContinuousAt g 0) (hg0 : 0 < g 0) (hg1 : g 0 < 1) :
    ContinuousAt (fun h => Jp (B.p h) (g h)) 0 := by
  have hIcc : Set.Icc (0 : ℝ) 1 ∈ 𝓝 (g 0) := Icc_mem_nhds hg0 hg1
  have hmem : ∀ᶠ h : ℝ in 𝓝 0, g h ∈ Set.Icc (0 : ℝ) 1 := hg hIcc
  have hev : (fun h => Jp (pStar d) (g h) + (ell (B.p h) - ell (pStar d)) * g h
      + (Jp (B.p h) 0 - Jp (pStar d) 0)) =ᶠ[𝓝 0] fun h => Jp (B.p h) (g h) := by
    filter_upwards [hmem, eventually_mem_window B] with h hgm hhb
    exact (Jp_eq_Jp_pStar_add hd (B.p_mem h hhb).1 (B.p_mem h hhb).2 hgm.1 hgm.2).symm
  have hJ : ContinuousAt (Jp (pStar d)) (g 0) :=
    (continuousOn_Jp_Icc (pStar_pos hd) (pStar_lt_one hd)).continuousAt hIcc
  have hRHS : ContinuousAt (fun h => Jp (pStar d) (g h) + (ell (B.p h) - ell (pStar d)) * g h
      + (Jp (B.p h) 0 - Jp (pStar d) 0)) 0 :=
    ((hJ.comp hg).add (((ell_p_continuousAt hd B).sub continuousAt_const).mul hg)).add
      ((Jp_p_zero_continuousAt hd B).sub continuousAt_const)
  exact hRHS.congr hev

/-- The normalising constant `κ_h` of `eq:first-variation` is continuous at `0`.  Its
two entropy arguments `s_h²` and `s_h t_h` both collapse to `r_* ∈ (0,1)`. -/
theorem kappaVal_continuousAt (hd : 2 ≤ d) (B : KKTFamily d) :
    ContinuousAt B.kappaVal 0 := by
  have hr0 : 0 < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  have es2 : B.sVal 0 ^ 2 = rStar d := by rw [sVal_zero]; exact uStar_sq hd
  have est : B.sVal 0 * B.tVal 0 = rStar d := by
    rw [sVal_zero, tVal_zero, ← uStar_sq hd]; ring
  have gs0 : (0 : ℝ) < B.sVal 0 ^ 2 := by rw [es2]; exact hr0
  have gs1 : B.sVal 0 ^ 2 < 1 := by rw [es2]; exact hr1
  have gc0 : (0 : ℝ) < B.sVal 0 * B.tVal 0 := by rw [est]; exact hr0
  have gc1 : B.sVal 0 * B.tVal 0 < 1 := by rw [est]; exact hr1
  have c1 : ContinuousAt (fun h : ℝ => Jp (B.p h) (B.sVal h ^ 2)) 0 :=
    Jp_comp_continuousAt hd B ((sVal_continuousAt B).pow 2) gs0 gs1
  have c2 : ContinuousAt (fun h : ℝ => Jp (B.p h) (B.sVal h * B.tVal h)) 0 :=
    Jp_comp_continuousAt hd B ((sVal_continuousAt B).mul (tVal_continuousAt B)) gc0 gc1
  have h : ContinuousAt (fun h : ℝ =>
      2 * (B.alph h * Jp (B.p h) (B.sVal h ^ 2)
          + (1 - B.alph h) * Jp (B.p h) (B.sVal h * B.tVal h))
        - B.etaVal h * B.sVal h ^ d) 0 :=
    (continuousAt_const.mul (((alph_continuousAt B).mul c1).add
      ((continuousAt_const.sub (alph_continuousAt B)).mul c2))).sub
        ((etaVal_continuousAt B).mul ((sVal_continuousAt B).pow d))
  exact h

/-! ## The limits at the singular endpoint

The same facts with the value at `0` substituted.  These are the forms
`thm:endpoint-optimizers` consumes: it asserts convergence of the parameter curve, not
continuity of a function that happens to be defined at `0`. -/

/-- **`p_h → p_*`.**  With `pcGlobal_rStar` this is the first coordinate of the limit
`(p_h, r_h) → (p_c(r_*), r_*)` of `thm:endpoint-optimizers`. -/
theorem tendsto_p (B : KKTFamily d) : Tendsto B.p (𝓝 (0 : ℝ)) (𝓝 (pStar d)) := by
  have h := (p_continuousAt B).tendsto
  rwa [B.p_zero] at h

/-- **`u_h → u_*`**, on the full neighbourhood of `0`. -/
theorem tendsto_u_nhds (B : KKTFamily d) : Tendsto B.u (𝓝 (0 : ℝ)) (𝓝 (uStar d)) := by
  have h := (u_continuousAt B).tendsto
  rwa [B.u_zero] at h

/-- **`γ_h → γ_*`**, on the full neighbourhood of `0`. -/
theorem tendsto_gam_nhds (B : KKTFamily d) :
    Tendsto B.gam (𝓝 (0 : ℝ)) (𝓝 (gammaStar d)) := by
  have h := (gam_continuousAt B).tendsto
  rwa [B.gam_zero] at h

variable {B : KKTFamily d}

open MeasureTheory

/-! ## The window is open -/

/-- The family window is a neighbourhood of each of its points.  Used wherever a local
property has to be transported from `h` to nearby parameters. -/
theorem eventually_window_of_mem {h : ℝ} (hh : |h| < B.h₀) :
    ∀ᶠ z : ℝ in 𝓝 h, |z| < B.h₀ :=
  (isOpen_lt continuous_abs continuous_const).mem_nhds hh

/-! ## Analyticity of the density -/

/-- `q_h = α_h s_h^d + (1-α_h) t_h^d` is analytic on the window: it is a polynomial in the
analytic fields `α_h` and `u_h` and the identity. -/
theorem analyticAt_qVal {h : ℝ} (hh : |h| < B.h₀) : AnalyticAt ℝ B.qVal h := by
  have hu := B.analyticAt_u h hh
  have ha := B.analyticAt_alph h hh
  have hs : AnalyticAt ℝ B.sVal h := hu.sub analyticAt_id
  have ht : AnalyticAt ℝ B.tVal h := hu.add analyticAt_id
  have hq : AnalyticAt ℝ
      (fun z : ℝ => B.alph z * B.sVal z ^ d + (1 - B.alph z) * B.tVal z ^ d) h :=
    (ha.mul (hs.pow d)).add ((analyticAt_const.sub ha).mul (ht.pow d))
  exact hq

/-- **`r_h = q_h^{2/d}` is analytic on the window.**  A real power of a *positive* analytic
function, so `r_h = exp((2/d)·log q_h)` on a neighbourhood, and both factors are analytic
there.  This is the clause of `thm:endpoint-optimizers` that calls `h ↦ (p_h, r_h)` an
analytic curve. -/
theorem analyticAt_rVal {h : ℝ} (hh : |h| < B.h₀) : AnalyticAt ℝ B.rVal h := by
  have hexp : AnalyticAt ℝ
      (fun z : ℝ => Real.exp (Real.log (B.qVal z) * (2 / (d : ℝ)))) h :=
    (((analyticAt_qVal hh).log (qVal_pos hh)).mul analyticAt_const).rexp'
  refine hexp.congr ?_
  filter_upwards [eventually_window_of_mem hh] with z hz
  exact (Real.rpow_def_of_pos (qVal_pos hz) _).symm

/-! ## The limit of the parameter curve -/

/-- **`p_h → p_c(r_*)`.**  `tendsto_p` gives `p_h → p_*`, and `pcGlobal_rStar` says
`p_* = p_c(r_*)` — the continuous extension of the Lubetzky–Zhao boundary curve to the
exceptional density, where no Lubetzky–Zhao boundary arc exists.

This is the join between the Section 5 layer and the boundary-curve layer of
`LZBoundary/Curve.lean`, and it is what lets the introduction phrase the limit as a point on the
phase boundary rather than as the bare constant `p_*`. -/
theorem tendsto_p_pcGlobal (hd : 2 ≤ d) (B : KKTFamily d) :
    Tendsto B.p (𝓝 (0 : ℝ)) (𝓝 (pcGlobal d (rStar d))) := by
  rw [pcGlobal_rStar hd]
  exact tendsto_p B

/-! ## The two structural adjectives -/

/-- **`W_h` is rank one.**  `W_h(x,y) = f_h(x) f_h(y)` with `f_h = s_h` on `[0, α_h]` and
`t_h` off it — everywhere, not merely almost everywhere. -/
theorem graphon_rankOne {h : ℝ} (hh : |h| < B.h₀) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ x y, (B.graphon hh).toFun x y = f x * f y := by
  classical
  refine ⟨fun x => if x ∈ Set.Icc (0 : ℝ) (B.alph h) then B.sVal h else B.tVal h, ?_, ?_, ?_⟩
  · exact measurable_const.ite measurableSet_Icc measurable_const
  · intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) (B.alph h) <;> simp only [hx, if_true, if_false]
    · exact ⟨(sVal_pos hh).le, (sVal_lt_one hh).le⟩
    · exact ⟨(tVal_pos hh).le, (tVal_lt_one hh).le⟩
  · intro x y
    show bipodalValue (Set.Icc 0 (B.alph h)) (B.sVal h ^ 2) (B.sVal h * B.tVal h)
        (B.tVal h ^ 2) (x, y) = _
    unfold bipodalValue
    by_cases hx : x ∈ Set.Icc (0 : ℝ) (B.alph h) <;>
      by_cases hy : y ∈ Set.Icc (0 : ℝ) (B.alph h) <;>
      simp only [hx, hy, if_true, if_false] <;> ring

/-- **`W_h` is bipodal**, with vertex class `[0, α_h]` and the three levels `s_h²`, `s_h t_h`,
`t_h²`.  Immediate from the definition of `B.graphon`; recorded because
`thm:endpoint-optimizers` names the adjective. -/
theorem graphon_isBipodal {h : ℝ} (hh : |h| < B.h₀) : IsBipodal (B.graphon hh) :=
  ⟨Set.Icc 0 (B.alph h), B.sVal h ^ 2, B.sVal h * B.tVal h, B.tVal h ^ 2, measurableSet_Icc,
    sq_sVal_mem hh, cross_mem hh, sq_tVal_mem hh, ae_of_all _ fun _ => rfl⟩

/-! ## Uniform convergence to the constant graphon at the exceptional density -/

/-- `W_h` takes only the three values `s_h²`, `s_h t_h`, `t_h²`, so its distance to the
constant `r_*` is bounded by the largest of the three moduli — pointwise, with no measure
theory. -/
theorem abs_graphon_sub_rStar_le {h : ℝ} (hh : |h| < B.h₀) (x y : ℝ) :
    |(B.graphon hh).toFun x y - rStar d| ≤
      max (|B.sVal h ^ 2 - rStar d|)
        (max (|B.sVal h * B.tVal h - rStar d|) (|B.tVal h ^ 2 - rStar d|)) := by
  classical
  show |bipodalValue (Set.Icc 0 (B.alph h)) (B.sVal h ^ 2) (B.sVal h * B.tVal h)
      (B.tVal h ^ 2) (x, y) - rStar d| ≤ _
  unfold bipodalValue
  by_cases hx : x ∈ Set.Icc (0 : ℝ) (B.alph h) <;>
    by_cases hy : y ∈ Set.Icc (0 : ℝ) (B.alph h) <;>
    simp only [hx, hy, if_true, if_false]
  · exact le_max_left _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- **`W_h → r_*` uniformly**, hence in `L^∞`: the closing clause of
`thm:endpoint-optimizers`.

All three edge values collapse to `r_* = u_*²` as `h → 0`, and `abs_graphon_sub_rStar_le`
turns that into a sup bound. -/
theorem exists_graphon_unif (hd : 2 ≤ d) (B : KKTFamily d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h : ℝ) (hh : |h| < B.h₀), |h| < δ →
      ∀ x y, |(B.graphon hh).toFun x y - rStar d| ≤ ε := by
  -- a continuous function of `h` with value `r_*` at `0` stays within `ε` of `r_*` nearby
  have key : ∀ g : ℝ → ℝ, ContinuousAt g 0 → g 0 = rStar d →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, |z| < δ → |g z - rStar d| ≤ ε := by
    intro g hg hg0
    have hev : ∀ᶠ z : ℝ in 𝓝 (0 : ℝ), |g z - rStar d| < ε := by
      have h := Metric.tendsto_nhds.mp hg.tendsto ε hε
      simpa [Real.dist_eq, hg0] using h
    obtain ⟨δ, hδ, hprop⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨δ, hδ, fun z hz => (hprop (by rwa [Real.dist_eq, sub_zero])).le⟩
  have hs0 : B.sVal 0 = uStar d := sVal_zero B
  have ht0 : B.tVal 0 = uStar d := tVal_zero B
  obtain ⟨δ₁, hδ₁, h₁⟩ := key (fun z => B.sVal z ^ 2) ((sVal_continuousAt B).pow 2)
    (show B.sVal 0 ^ 2 = rStar d by rw [hs0]; exact uStar_sq hd)
  obtain ⟨δ₂, hδ₂, h₂⟩ := key (fun z => B.sVal z * B.tVal z)
    ((sVal_continuousAt B).mul (tVal_continuousAt B))
    (show B.sVal 0 * B.tVal 0 = rStar d by rw [hs0, ht0, ← uStar_sq hd]; ring)
  obtain ⟨δ₃, hδ₃, h₃⟩ := key (fun z => B.tVal z ^ 2) ((tVal_continuousAt B).pow 2)
    (show B.tVal 0 ^ 2 = rStar d by rw [ht0]; exact uStar_sq hd)
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun h hh hlt x y => ?_⟩
  refine le_trans (abs_graphon_sub_rStar_le hh x y) ?_
  refine max_le (h₁ h (lt_of_lt_of_le hlt (min_le_left _ _)))
    (max_le (h₂ h (lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_left _ _))))
      (h₃ h (lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_right _ _)))))

end KKTFamily

end UpperTailOptimizers
