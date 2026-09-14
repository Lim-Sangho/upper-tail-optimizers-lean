import UpperTailOptimizers.NonexceptionalEndpoint.Proof.Main
import UpperTailOptimizers.NonexceptionalEndpoint.QuadraticGrowth.AnalyticExtension

/-!
# The coefficient `A_H` is the second `δ`-derivative of the analytic extension

`thm:positive-second-variation` of `paper/paper.tex` constructs a real-analytic extension `G` of
the boundary excess `G_r(δ) = I_{pc(r),r}(r-δ) - J_{pc(r)}(r)` across `δ = 0` and defines
`A_H(r) := ∂²_δG(r,0)`.  `AHGlobal` (`NonexceptionalEndpoint/Proof/Main.lean`) is defined instead as the
limit of `2G_r(δ)/δ²` as `δ ↓ 0`, which does not refer to a choice of extension.
`dDelta_dDelta_eq_AHGlobal` shows that the two definitions agree: for **every** `G` analytic at
`(r,0)` that agrees with `G_r(δ)` for small `δ > 0`, `∂²_δG(r,0) = AHGlobal H d r`.

The proof compares `G` with the extension of `positive_second_variation` on the single
density `r`: the two `δ`-slices are analytic at `0` and agree for small `δ > 0`, so by the
isolated-zeros principle they agree near `0`, and so do their second derivatives.
-/

namespace UpperTailOptimizers

open Real Set Filter Topology

/-- For `F` analytic at `(r,0)`, the iterated partial `δ`-derivative is the second derivative of
the slice `s ↦ F(r,s)` at `0`. -/
theorem dDelta_dDelta_eq_deriv_deriv {F : ℝ × ℝ → ℝ} {r : ℝ} (hF : AnalyticAt ℝ F (r, 0)) :
    dDelta (dDelta F) (r, 0) = deriv (deriv fun s => F (r, s)) 0 := by
  have hslice : Continuous fun s : ℝ => ((r, s) : ℝ × ℝ) := by fun_prop
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), AnalyticAt ℝ F (r, s) :=
    hslice.continuousAt.eventually (hF.eventually_analyticAt)
  have heq : (fun s => dDelta F (r, s)) =ᶠ[𝓝 (0 : ℝ)] deriv fun s => F (r, s) := by
    filter_upwards [hev] with s hs
    exact ((hasDerivAt_dDelta hs.differentiableAt).deriv).symm
  rw [← heq.deriv_eq]
  exact ((hasDerivAt_dDelta (analyticAt_dDelta hF).differentiableAt).deriv).symm

/-- **`A_H(r) = ∂²_δG(r,0)`** for every analytic extension `G` of the boundary excess
(`thm:positive-second-variation`).  Let `r ∈ (0,1) ∖ {r_*}` and let `G` be analytic at `(r,0)`
with `G(r,δ) = I_{pc(r),r}(r-δ) - J_{pc(r)}(r)` for `0 < δ < δ₁`.  Then
`∂²_δG(r,0) = AHGlobal H d r`. -/
theorem dDelta_dDelta_eq_AHGlobal {d : ℕ} (hd : 2 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hreg : ∀ x, H.degree x = d)
    (hm : 1 ≤ H.edgeFinset.card) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hr : r ≠ rStar d)
    {G : ℝ × ℝ → ℝ} (hG : AnalyticAt ℝ G (r, 0)) {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hGeq : ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      (G (r, δ) : EReal)
        = reducedObjective H (pcGlobal d r) r (r - δ) - (Jp (pcGlobal d r) r : EReal)) :
    dDelta (dDelta G) (r, 0) = AHGlobal H d r := by
  obtain ⟨M, hrM, -⟩ := lz_boundary_arcs hd hr0 hr1 hr
  have hK : ({r} : Set ℝ) ⊆ M.U := Set.singleton_subset_iff.mpr hrM
  obtain ⟨δbar, -, -, -, N, G₀, hδbar, -, -, -, -, hNmem, hGana, hGagree, -, -, hd2G0, -, -⟩ :=
    positive_second_variation hd M hK isCompact_singleton ⟨r, rfl⟩
      (fun s hs => (Set.mem_singleton_iff.mp hs) ▸ hr) H hreg hm
  -- on `0 < δ < min δ₁ δbar` the two functions agree
  have hagree : ∀ δ : ℝ, 0 < δ → δ < min δ₁ δbar → G (r, δ) = G₀ (r, δ) := by
    intro δ hδ0 hδ
    have h := hGeq δ hδ0 (lt_of_lt_of_le hδ (min_le_left _ _))
    have hne : ∃ W : Graphon, W.edgeDensity = r - δ ∧
        W.tDensity H = r ^ H.edgeFinset.card := by
      by_contra hempty
      rw [reducedObjective_eq_top H hempty, EReal.top_sub_coe] at h
      exact EReal.coe_ne_top _ h
    rw [reducedObjective_eq_coe H hne, ← EReal.coe_sub, EReal.coe_eq_coe_iff] at h
    rw [h, hGagree r rfl δ hδ0 (lt_of_lt_of_le hδ (min_le_right _ _)), boundaryExcess,
      pcGlobal_eq_pc hd M hrM]
  -- the two slices are analytic at `0` and agree on a right neighbourhood, hence near `0`
  have hpair : AnalyticAt ℝ (fun s : ℝ => ((r, s) : ℝ × ℝ)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hG₀ : AnalyticAt ℝ G₀ (r, 0) := hGana _ (hNmem r rfl 0 (by rw [abs_zero]; exact hδbar))
  have hg : AnalyticAt ℝ (fun s => G (r, s)) 0 := hG.comp hpair
  have hg₀ : AnalyticAt ℝ (fun s => G₀ (r, s)) 0 := hG₀.comp hpair
  have hfreq : ∃ᶠ s in 𝓝[≠] (0 : ℝ), G (r, s) = G₀ (r, s) := by
    have hright : ∀ᶠ s in 𝓝[>] (0 : ℝ), G (r, s) = G₀ (r, s) := by
      filter_upwards [Ioo_mem_nhdsGT (lt_min hδ₁ hδbar)] with s hs
      exact hagree s hs.1 hs.2
    exact (hright.frequently).filter_mono (nhdsWithin_mono _ fun s hs => ne_of_gt hs)
  have heq : (fun s => G (r, s)) =ᶠ[𝓝 (0 : ℝ)] fun s => G₀ (r, s) := by
    rcases hg.eventually_eq_or_eventually_ne hg₀ with h | h
    · exact h
    · exact absurd (hfreq.and_eventually h) (by simp)
  have hderiv : deriv (fun s => G (r, s)) =ᶠ[𝓝 (0 : ℝ)] deriv fun s => G₀ (r, s) :=
    heq.eventuallyEq_nhds.mono fun s hs => hs.deriv_eq
  rw [dDelta_dDelta_eq_deriv_deriv hG, hderiv.deriv_eq, ← dDelta_dDelta_eq_deriv_deriv hG₀,
    hd2G0 r rfl, AH_eq_AHGlobal H hd M hrM]

end UpperTailOptimizers
