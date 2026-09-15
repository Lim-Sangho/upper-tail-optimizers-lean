import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.KernelError
import UpperTailOptimizers.SingularEndpoint.AuxiliaryLagrangian.DistributionQuant

/-!
# The window package for the quantitative half of `lem:auxiliary-lagrangian-bound` (Section 5)

`KKTFamily.distributionGap_lower` (`SingularEndpoint/AuxiliaryLagrangian/DistributionQuant.lean`) assembles the gap bound of
the refined form of `eq:auxiliary-lagrangian-bound` with the mixed and tail terms still exact.  It was stated with a long list of hypotheses that were
deferred when it was written:

* both atoms `s_h`, `t_h` in the central window `𝓝_ρ`;
* the four coefficient bounds `|p_{00,h}|, |p_{d0,h}|, |p_{0d,h}|, |p_{dd,h}| ≤ Cp` and the
  two one-variable bounds `|u_{0,h}|, |u_{d,h}| ≤ Cu` on `𝓝_ρ` — the Lean form, at the chosen
  radius, of the bound `max{|p_{ij,h}|, |u_{i,h}(x)|, |v_{i,h}(y)|} ≤ C_d` in the proof of
  `lem:central-kernel-bound` (the `v_{i,h}` coincide with the `u_{i,h}` by symmetry of the
  kernel);
* the corner error `|Θ_h(x,y) - d³/4| ≤ δ` with `δ ≤ a/8 = d³/192`, `a = d³/24` (the proof of
  `lem:central-kernel-bound` only needs the accuracy `a/4`);
* the quartic first-variation bound `(d³/24)Q_h² ≤ Ψ̃_h` of `lem:first-variation-bound`;
* the entropy bound `sup_{[0,4]}|J̃_{p_h}| ≤ C` (the paper's `‖J̃_{p_h}‖_{L^∞([0,4])} ≤ C_d` of
  `lem:continuation-kernel-bounds`).

Each of them is now proved elsewhere in the development, and **this file discharges them all
at once**.  The one point that needs care is the *quantifier order in `ρ`*:
`exists_kernelTheta_error` produces its own radius `ρ₀` for a prescribed accuracy `ε`,
whereas the six boundedness lemmas and `exists_atoms_mem_centralWindow` hold for a *given*
radius.  The package therefore fixes `ε = d³/192` first, obtains `ρ₀`, and only then chooses

  `ρ = min (min ρ₀ (u_*/2)) (min ((1-u_*)/2) w)`,

`w` being the first-variation radius.  Shrinking is harmless for the corner bound because the window
is monotone in its radius — `centralWindow_subset_of_le`, proved explicitly below — and it is
harmless for the first-variation bound because `exists_firstVariation_lower_PsiT` already quantifies over
all admissible `ρ`.  Nothing here needs the reverse implication, so no lemma has to be
restated.

## Where this file sits

`distributionGap_lower_window` below is exactly `distributionGap_lower` with its hypotheses discharged;
the mixed and tail terms are still exact, so it is not yet `eq:auxiliary-lagrangian-bound`.  The
Young absorption that turns them into `ζ(h)ε_ρ`, `ε_ρ = ν(T_ρ)` (a step of this closed-window route with no
counterpart in the paper, whose mixed-rectangle bound is `C_dh^{1/2}ν(𝒯_ρ) + C_dν(𝒯_ρ)²`) is
`SingularEndpoint/AuxiliaryLagrangian/DistributionAbsorption.lean` (`exists_distributionGap_refined` =
the refined form, `exists_distributionGap` = `eq:auxiliary-lagrangian-bound`), and
`SingularEndpoint/AuxiliaryLagrangian/DistributionFinal.lean` combines that with this package into the hypothesis-free
`exists_distributionGap_refined_window`, `exists_distributionGap_refined_window_forall` and
`exists_distributionGap_window`.

## Contents

* `centralWindow_subset_of_le` — `ρ' ≤ ρ → 𝓝_{ρ'} ⊆ 𝓝_ρ`;
* `KKTFamily.DistributionWindow` — the bundled hypothesis list of `distributionGap_lower`, at a
  fixed window radius `ρ`, fixed constants `Cu` (the one-variable
  functions), `Cp` (the coefficients) and `C`, and a fixed `h`;
* **`KKTFamily.exists_distribution_window`** — the package: a radius, the constants and a
  threshold for which `DistributionWindow` holds at every small `h > 0`;
* **`KKTFamily.exists_distribution_window_forall`** — the same at *every* radius below a
  threshold, which is what the closed-window assembly of `lem:graphon-lagrangian-bound`
  (`SingularEndpoint/GraphonComparison/GraphonComparisonMaster.lean`) needs;
* **`KKTFamily.distributionGap_lower_window`** — `distributionGap_lower` with no remaining
  mathematical hypotheses beyond `2 ≤ d`, smallness of `h`, and `ν` being a probability
  measure carried by `[0,2]`.
-/

namespace UpperTailOptimizers

open MeasureTheory

variable {d : ℕ}

/-- **Shrinking the radius shrinks the window.**  `𝓝_ρ = [u_* - ρ, u_* + ρ]` is monotone in
`ρ`, so a bound proved on `𝓝_ρ` is inherited by `𝓝_{ρ'}` for every `ρ' ≤ ρ`.  This is what
makes `exists_kernelTheta_error` — which produces its *own* radius — combinable with the
lemmas that hold at a prescribed radius. -/
theorem centralWindow_subset_of_le (d : ℕ) {ρ ρ' : ℝ} (hρ : ρ' ≤ ρ) :
    centralWindow d ρ' ⊆ centralWindow d ρ := by
  show Set.Icc (uStar d - ρ') (uStar d + ρ') ⊆ Set.Icc (uStar d - ρ) (uStar d + ρ)
  exact Set.Icc_subset_Icc (by linarith) (by linarith)

namespace KKTFamily

/-- **The hypothesis list of `distributionGap_lower`, bundled.**  The fields are exactly the
deferred hypotheses of `KKTFamily.distributionGap_lower`, at window radius `ρ`, one-variable
constant `Cu`, coefficient constant `Cp`, entropy constant `C` and parameter `h`; the corner
accuracy is fixed at the largest value `distributionGap_lower` accepts, `δ = a/8 = d³/192`.
`exists_distribution_window` produces all of them together. -/
structure DistributionWindow (B : KKTFamily d) (ρ Cu Cp C h : ℝ) : Prop where
  /-- The left atom lies in the central window. -/
  sVal_mem : B.sVal h ∈ centralWindow d ρ
  /-- The right atom lies in the central window. -/
  tVal_mem : B.tVal h ∈ centralWindow d ρ
  /-- The constant coefficient of `P_h` is bounded by `Cp`. -/
  kp00_le : |B.kp00 h| ≤ Cp
  /-- The `x^d` coefficient of `P_h` is bounded by `Cp`. -/
  kpd0_le : |B.kpd0 h| ≤ Cp
  /-- The `y^d` coefficient of `P_h` is bounded by `Cp`. -/
  kp0d_le : |B.kp0d h| ≤ Cp
  /-- The `x^dy^d` coefficient of `P_h` is bounded by `Cp`. -/
  kpdd_le : |B.kpdd h| ≤ Cp
  /-- The one-variable function `u_{0,h}` is bounded by `Cu` on the window. -/
  u0_le : ∀ x ∈ centralWindow d ρ, |B.u0 h x| ≤ Cu
  /-- The one-variable function `u_{d,h}` is bounded by `Cu` on the window. -/
  ud_le : ∀ x ∈ centralWindow d ρ, |B.ud h x| ≤ Cu
  /-- The corner error of `lem:central-kernel-bound` at accuracy `a/8 = d³/192`. -/
  tailSq_le : ∀ x ∈ centralWindow d ρ, ∀ y ∈ centralWindow d ρ,
    |B.kernelTheta h x y - (d : ℝ) ^ 3 / 4| ≤ (d : ℝ) ^ 3 / 192
  /-- The quartic first-variation bound for the continued potential, with `a = d³/24`. -/
  firstVariation_le : ∀ x ∈ centralWindow d ρ, (d : ℝ) ^ 3 / 24 * B.Qh h x ^ 2 ≤ B.PsiT h x
  /-- The crude entropy bound `sup_{[0,4]}|J̃_{p_h}| ≤ C`. -/
  JpTildeH_le : ∀ z ∈ Set.Icc (0 : ℝ) 4, |B.JpTildeH h z| ≤ C

/-- **The window package.**  There are a radius `ρ > 0` admissible for the window arithmetic
(`ρ ≤ u_*/2` and `ρ ≤ (1-u_*)/2`), constants `Cu, Cp, C > 0` and a threshold `hρ > 0` such
that every hypothesis of `distributionGap_lower` holds simultaneously at every `0 < h < hρ` with
`|h| < h₀`.

The construction is the one described in the module docstring: `exists_kernelTheta_error` is
called first, at `ε = d³/192`, and its radius `ρ₀` is intersected with `u_*/2`, `(1-u_*)/2`
and the first-variation radius `w` of `exists_firstVariation_lower_PsiT`; the resulting `ρ` is then fed to
`exists_kp00_window`, `exists_kpd0_window`, `exists_kp0d_window`, `exists_kpdd_window`,
`exists_u0_window`, `exists_ud_window` and `exists_atoms_mem_centralWindow`.  The corner bound
survives the shrinking by `centralWindow_subset_of_le`.  `Cp` is the maximum of the four
coefficient constants, `Cu` the maximum of the two one-variable ones, `C` comes from
`exists_abs_JpTildeH_le`, and `hρ` is the minimum of the ten thresholds.

The radius is additionally capped at an arbitrary `ρmax > 0`.  That costs nothing here — `ρ`
was already a minimum — and it is what lets a consumer that manufactures its own radius (the
rare-row layer of `lem:graphon-lagrangian-bound` does) intersect the two.  `exists_distribution_window`
below is this statement at `ρmax = 1`. -/
theorem exists_distribution_window_le (hd : 2 ≤ d) (B : KKTFamily d) {ρmax : ℝ}
    (hρmax : 0 < ρmax) :
    ∃ ρ > 0, ∃ Cu > 0, ∃ Cp > 0, ∃ C > 0, ∃ hρ > 0,
      ρ ≤ uStar d / 2 ∧ ρ ≤ (1 - uStar d) / 2 ∧ ρ ≤ ρmax ∧
        ∀ h : ℝ, 0 < h → h < hρ → |h| < B.h₀ → B.DistributionWindow ρ Cu Cp C h := by
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hεpos : (0 : ℝ) < (d : ℝ) ^ 3 / 192 := div_pos (pow_pos hdpos 3) (by norm_num)
  obtain ⟨ρ₀, hρ₀, δc, hδc, hcorner⟩ :=
    exists_kernelTheta_error hd B ((d : ℝ) ^ 3 / 192) hεpos
  obtain ⟨w, hw, δtw, hδtw, htw⟩ := exists_firstVariation_lower_PsiT hd B
  obtain ⟨ρ, hρpos, hρρ₀, hρu, hρ1, hρw, hρmx⟩ :
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ρ ≤ uStar d / 2 ∧ ρ ≤ (1 - uStar d) / 2 ∧ ρ ≤ w ∧
        ρ ≤ ρmax :=
    ⟨min (min (min ρ₀ (uStar d / 2)) (min ((1 - uStar d) / 2) w)) ρmax,
      lt_min (lt_min (lt_min hρ₀ (by linarith)) (lt_min (by linarith) hw)) hρmax,
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)),
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)),
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)),
      min_le_right _ _⟩
  obtain ⟨C00, hC00, δ00, hδ00, hb00⟩ := exists_kp00_window hd B hρpos hρu hρ1
  obtain ⟨Cd0, -, δd0, hδd0, hbd0⟩ := exists_kpd0_window hd B hρpos hρu hρ1
  obtain ⟨C0d, -, δ0d, hδ0d, hb0d⟩ := exists_kp0d_window hd B hρpos hρu hρ1
  obtain ⟨Cdd, -, δdd, hδdd, hbdd⟩ := exists_kpdd_window hd B hρpos hρu hρ1
  obtain ⟨Cu0, hCu0, δu0, hδu0, hbu0⟩ := exists_u0_window hd B hρpos hρu hρ1
  obtain ⟨Cud, -, δud, hδud, hbud⟩ := exists_ud_window hd B hρpos hρu hρ1
  obtain ⟨δa, hδa, hatoms⟩ := exists_atoms_mem_centralWindow B hρpos
  obtain ⟨CJ, hCJ, δJ, hδJ, hJ⟩ := exists_abs_JpTildeH_le hd B
  refine ⟨ρ, hρpos, max Cu0 Cud, lt_of_lt_of_le hCu0 (le_max_left _ _),
    max (max C00 Cd0) (max C0d Cdd),
    lt_of_lt_of_le hC00 (le_trans (le_max_left _ _) (le_max_left _ _)), CJ, hCJ,
    min δc (min δtw (min δ00 (min δd0 (min δ0d (min δdd (min δu0 (min δud (min δa δJ)))))))),
    ?_, hρu, hρ1, hρmx, ?_⟩
  · simp only [lt_min_iff]
    exact ⟨hδc, hδtw, hδ00, hδd0, hδ0d, hδdd, hδu0, hδud, hδa, hδJ⟩
  intro h hh0 hhlt hhb
  simp only [lt_min_iff] at hhlt
  obtain ⟨hlc, hltw, hl00, hld0, hl0d, hldd, hlu0, hlud, hla, hlJ⟩ := hhlt
  obtain ⟨hs, ht⟩ := hatoms h hh0 hla
  exact
    { sVal_mem := hs
      tVal_mem := ht
      kp00_le := le_trans (hb00 h hh0 hl00) (le_trans (le_max_left _ _) (le_max_left _ _))
      kpd0_le := le_trans (hbd0 h hh0 hld0) (le_trans (le_max_right _ _) (le_max_left _ _))
      kp0d_le := le_trans (hb0d h hh0 hl0d) (le_trans (le_max_left _ _) (le_max_right _ _))
      kpdd_le := le_trans (hbdd h hh0 hldd) (le_trans (le_max_right _ _) (le_max_right _ _))
      u0_le := fun x hx => le_trans (hbu0 h hh0 hlu0 x hx) (le_max_left _ _)
      ud_le := fun x hx => le_trans (hbud h hh0 hlud x hx) (le_max_right _ _)
      tailSq_le := fun x hx y hy => hcorner h hh0 hlc x (centralWindow_subset_of_le d hρρ₀ hx)
        y (centralWindow_subset_of_le d hρρ₀ hy)
      firstVariation_le := htw h hh0 hltw hhb ρ hρw hρu hρ1
      JpTildeH_le := hJ h (by rwa [abs_of_pos hh0]) }

/-- **The window package**, in the form most consumers want: no upper bound on `ρ` is imposed.
This is `exists_distribution_window_le` at `ρmax = 1`, with the extra conjunct dropped. -/
theorem exists_distribution_window (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ > 0, ∃ Cu > 0, ∃ Cp > 0, ∃ C > 0, ∃ hρ > 0,
      ρ ≤ uStar d / 2 ∧ ρ ≤ (1 - uStar d) / 2 ∧
        ∀ h : ℝ, 0 < h → h < hρ → |h| < B.h₀ → B.DistributionWindow ρ Cu Cp C h := by
  obtain ⟨ρ, hρpos, Cu, hCu, Cp, hCp, C, hC, hth, hthpos, hρu, hρ1, -, hwin⟩ :=
    exists_distribution_window_le hd B (ρmax := 1) one_pos
  exact ⟨ρ, hρpos, Cu, hCu, Cp, hCp, C, hC, hth, hthpos, hρu, hρ1, hwin⟩

/-- **The window package at every small enough radius.**  `exists_distribution_window_le` caps the
radius at a prescribed `ρmax`, but returns a radius *strictly inside* that cap, not the cap
itself.  That is not enough for the assembly of `lem:graphon-lagrangian-bound` in
`SingularEndpoint/GraphonComparison/GraphonComparisonMaster.lean`: the law half
and the residual half each manufacture a radius, and the two must be made **equal**, which
needs a bound valid at *every* small enough radius.

Unlike the multiplier bound of `SingularEndpoint/GraphonComparison/GraphonComparisonMain.lean`, this one is not free by
monotonicity — `sVal_mem` and `tVal_mem` require the atoms to *lie in* `𝓝_ρ`, which shrinking
`ρ` makes harder.  What saves it is the quantifier order: the threshold `hρ` is chosen after
`ρ`, and `exists_atoms_mem_centralWindow` supplies one for each `ρ > 0`. -/
theorem exists_distribution_window_forall (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ₀ > 0, ρ₀ ≤ uStar d / 2 ∧ ρ₀ ≤ (1 - uStar d) / 2 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
        ∃ Cu > 0, ∃ Cp > 0, ∃ C > 0, ∃ hρ > 0,
          ∀ h : ℝ, 0 < h → h < hρ → |h| < B.h₀ → B.DistributionWindow ρ Cu Cp C h := by
  have hdpos : (0 : ℝ) < (d : ℝ) := dpos hd
  have hu0 : 0 < uStar d := uStar_pos hd
  have hu1 : uStar d < 1 := uStar_lt_one hd
  have hεpos : (0 : ℝ) < (d : ℝ) ^ 3 / 192 := div_pos (pow_pos hdpos 3) (by norm_num)
  obtain ⟨ρk, hρk, δc, hδc, hcorner⟩ :=
    exists_kernelTheta_error hd B ((d : ℝ) ^ 3 / 192) hεpos
  obtain ⟨w, hw, δtw, hδtw, htw⟩ := exists_firstVariation_lower_PsiT hd B
  refine ⟨min (min ρk (uStar d / 2)) (min ((1 - uStar d) / 2) w),
    lt_min (lt_min hρk (by linarith)) (lt_min (by linarith) hw),
    le_trans (min_le_left _ _) (min_le_right _ _),
    le_trans (min_le_right _ _) (min_le_left _ _), ?_⟩
  intro ρ hρpos hρle
  have hρρk : ρ ≤ ρk := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρu : ρ ≤ uStar d / 2 :=
    le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ1 : ρ ≤ (1 - uStar d) / 2 :=
    le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρw : ρ ≤ w := le_trans hρle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨C00, hC00, δ00, hδ00, hb00⟩ := exists_kp00_window hd B hρpos hρu hρ1
  obtain ⟨Cd0, -, δd0, hδd0, hbd0⟩ := exists_kpd0_window hd B hρpos hρu hρ1
  obtain ⟨C0d, -, δ0d, hδ0d, hb0d⟩ := exists_kp0d_window hd B hρpos hρu hρ1
  obtain ⟨Cdd, -, δdd, hδdd, hbdd⟩ := exists_kpdd_window hd B hρpos hρu hρ1
  obtain ⟨Cu0, hCu0, δu0, hδu0, hbu0⟩ := exists_u0_window hd B hρpos hρu hρ1
  obtain ⟨Cud, -, δud, hδud, hbud⟩ := exists_ud_window hd B hρpos hρu hρ1
  obtain ⟨δa, hδa, hatoms⟩ := exists_atoms_mem_centralWindow B hρpos
  obtain ⟨CJ, hCJ, δJ, hδJ, hJ⟩ := exists_abs_JpTildeH_le hd B
  refine ⟨max Cu0 Cud, lt_of_lt_of_le hCu0 (le_max_left _ _),
    max (max C00 Cd0) (max C0d Cdd),
    lt_of_lt_of_le hC00 (le_trans (le_max_left _ _) (le_max_left _ _)), CJ, hCJ,
    min δc (min δtw (min δ00 (min δd0 (min δ0d (min δdd (min δu0 (min δud (min δa δJ)))))))),
    ?_, ?_⟩
  · simp only [lt_min_iff]
    exact ⟨hδc, hδtw, hδ00, hδd0, hδ0d, hδdd, hδu0, hδud, hδa, hδJ⟩
  intro h hh0 hhlt hhb
  simp only [lt_min_iff] at hhlt
  obtain ⟨hlc, hltw, hl00, hld0, hl0d, hldd, hlu0, hlud, hla, hlJ⟩ := hhlt
  obtain ⟨hs, ht⟩ := hatoms h hh0 hla
  exact
    { sVal_mem := hs
      tVal_mem := ht
      kp00_le := le_trans (hb00 h hh0 hl00) (le_trans (le_max_left _ _) (le_max_left _ _))
      kpd0_le := le_trans (hbd0 h hh0 hld0) (le_trans (le_max_right _ _) (le_max_left _ _))
      kp0d_le := le_trans (hb0d h hh0 hl0d) (le_trans (le_max_left _ _) (le_max_right _ _))
      kpdd_le := le_trans (hbdd h hh0 hldd) (le_trans (le_max_right _ _) (le_max_right _ _))
      u0_le := fun x hx => le_trans (hbu0 h hh0 hlu0 x hx) (le_max_left _ _)
      ud_le := fun x hx => le_trans (hbud h hh0 hlud x hx) (le_max_right _ _)
      tailSq_le := fun x hx y hy => hcorner h hh0 hlc x (centralWindow_subset_of_le d hρρk hx)
        y (centralWindow_subset_of_le d hρρk hy)
      firstVariation_le := htw h hh0 hltw hhb ρ hρw hρu hρ1
      JpTildeH_le := hJ h (by rwa [abs_of_pos hh0]) }

/-- **`distributionGap_lower` with every mathematical hypothesis discharged.**  Writing
`A_ρ = ∫_{𝓝_ρ}Q_h²dν`, `ε_ρ = ν(T_ρ)` and `Δ = ∫x^ddν - q_h`, there are a window radius
`ρ > 0`, a constant `M > 0` and a threshold `hρ > 0` such that for every `0 < h < hρ` with
`|h| < h₀` and every probability measure `ν` carried by `[0,2]`,

`(d³/32)A_ρ + ∫_{T_ρ}Ψ̃_hdν - M{(1+2^d)ε_ρ + |Δ|}² + 2∬_{𝓝_ρ×T_ρ}K_hdσdσ + ∬_{T_ρ²}K_hdσdσ
   ≤ 𝒥_h(ν) - 𝒥_h(ν_h) - η_hΔ`.

`M = C_p + 192C_u²/d³` is the constant of `distributionGap_lower`, built from the coefficient and
one-variable constants `Cp`, `Cu` of the window package.
This is the refined form of `eq:auxiliary-lagrangian-bound` with the mixed and tail terms still exact, so it is
not yet `eq:auxiliary-lagrangian-bound`; the Young absorption (not in the paper) that turns them into `ζ(h)ε_ρ` is
`KKTFamily.exists_distributionGap_refined`
(`SingularEndpoint/AuxiliaryLagrangian/DistributionAbsorption.lean`), and the two are joined in `SingularEndpoint/AuxiliaryLagrangian/DistributionFinal.lean`. -/
theorem distributionGap_lower_window (hd : 2 ≤ d) (B : KKTFamily d) :
    ∃ ρ > 0, ∃ M > 0, ∃ hρ > 0, ∀ h : ℝ, 0 < h → h < hρ → |h| < B.h₀ →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 2)ᶜ = 0 →
        (d : ℝ) ^ 3 / 32 * (∫ x in centralWindow d ρ, B.Qh h x ^ 2 ∂ν)
            + (∫ x in Set.Icc (0 : ℝ) 2 \ centralWindow d ρ, B.PsiT h x ∂ν)
            - M * ((1 + 2 ^ d) * (ν (Set.Icc (0 : ℝ) 2 \ centralWindow d ρ)).toReal
                + |(∫ x, x ^ d ∂ν) - B.qVal h|) ^ 2
            + (2 * B.mixedQuad h ρ ν + B.tailQuad h ρ ν)
          ≤ B.distributionJ h ν - B.distributionJ h (B.distributionMeasure h)
              - B.etaVal h * ((∫ x, x ^ d ∂ν) - B.qVal h) := by
  obtain ⟨ρ, hρpos, Cu, hCu, Cp, hCp, C, hC, hth, hthpos, hρu, hρ1, hwin⟩ :=
    exists_distribution_window hd B
  have hδ0 : (0 : ℝ) ≤ (d : ℝ) ^ 3 / 192 := by positivity
  refine ⟨ρ, hρpos, Cp + 192 * Cu ^ 2 / (d : ℝ) ^ 3, ?_, hth, hthpos, ?_⟩
  · have hnn : (0 : ℝ) ≤ 192 * Cu ^ 2 / (d : ℝ) ^ 3 := by positivity
    linarith
  intro h hh0 hhlt hhb ν hνp hν
  have := hνp
  obtain ⟨hs, ht, h00, hd0, h0d, hdd, hu0, hud, hcorner, htw, hJ⟩ := hwin h hh0 hhlt hhb
  exact distributionGap_lower hd B hhb hh0 hρu hρ1 hν hs ht hδ0 le_rfl hCu.le hCp.le h00 hd0 h0d
    hdd hu0 hud hcorner htw hJ

end KKTFamily

end UpperTailOptimizers
