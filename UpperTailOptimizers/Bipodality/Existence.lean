import UpperTailOptimizers.Graphon.Attainment
import UpperTailOptimizers.Graphon.Functionals

/-!
# Existence of fixed-density entropy maximizers

If some graphon has edge density `ε` and `H`-density `τ`, then the entropy attains its
supremum on `{W : e(W) = ε, t(H,W) = τ}`.  This is `kb:lem:exists` of the bipodality draft.
The proof is the direct method: a maximizing sequence has a cut-convergent subsequence, the two
densities pass to the limit, and upper semicontinuity of the entropy is lower semicontinuity of
`I_{1/2} = -2s + log 2`.
-/

namespace UpperTailOptimizers

open MeasureTheory Filter Topology

theorem exists_entropy_maximizer {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {ε τ : ℝ}
    (hne : ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ) :
    ∃ Wmax : Graphon, Wmax.edgeDensity = ε ∧ Wmax.tDensity H = τ ∧
      ∀ W : Graphon, W.edgeDensity = ε → W.tDensity H = τ → W.entropy ≤ Wmax.entropy := by
  classical
  set S : Set ℝ := {s | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ W.entropy = s}
    with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨W, h1, h2⟩ := hne
    exact ⟨W.entropy, W, h1, h2, rfl⟩
  have hSbdd : BddAbove S := ⟨(1 / 2) * Real.log 2, by
    rintro s ⟨W, -, -, rfl⟩; exact entropy_le W⟩
  set σ : ℝ := sSup S with hσ
  have hex : ∀ n : ℕ, ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
      σ - 1 / ((n : ℝ) + 1) < W.entropy := by
    intro n
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨s, ⟨W, h1, h2, rfl⟩, hlt⟩ :=
      exists_lt_of_lt_csSup hSne (show σ - 1 / ((n : ℝ) + 1) < σ by linarith)
    exact ⟨W, h1, h2, hlt⟩
  choose W hWe hWt hWs using hex
  obtain ⟨φ, Wlim, hφ, hcut⟩ := cut_seqCompact W
  have he : Wlim.edgeDensity = ε := by
    have h := edgeDensity_cutContinuous hcut
    have hc : Tendsto (fun k => (W (φ k)).edgeDensity) atTop (𝓝 ε) := by
      simp only [hWe]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h hc
  have ht : Wlim.tDensity H = τ := by
    have h := tDensity_cutContinuous H hcut
    have hc : Tendsto (fun k => (W (φ k)).tDensity H) atTop (𝓝 τ) := by
      simp only [hWt]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h hc
  refine ⟨Wlim, he, ht, fun W' h1 h2 => ?_⟩
  have hle : W'.entropy ≤ σ := le_csSup hSbdd ⟨W', h1, h2, rfl⟩
  suffices hge : σ ≤ Wlim.entropy by linarith
  refine le_of_forall_pos_le_add (fun η hη => ?_)
  -- eventually `s(W (φ k)) > σ - η`, i.e. `I_{1/2}(W (φ k)) < -2(σ - η) + log 2`
  have hIp : ∀ U : Graphon, U.Ip (1 / 2) = -2 * U.entropy + Real.log 2 := by
    intro U
    rw [U.Ip_eq_entropy (by norm_num) (by norm_num)]
    have h12 : (1:ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h12, div_self (by norm_num : (1:ℝ) / 2 ≠ 0), Real.log_one, mul_zero, add_zero,
      show (1:ℝ) / 2 = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have hev : ∀ᶠ k in atTop, (W (φ k)).Ip (1 / 2) ≤ -2 * (σ - η) + Real.log 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hφk : (N : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast le_trans hk (hφ.id_le k)
    have hsmall : 1 / ((φ k : ℝ) + 1) ≤ η := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 / η < (φ k : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hη] at this
      linarith
    have := hWs (φ k)
    rw [hIp]
    linarith
  have hlim := Ip_cut_lowerSemicontinuous (by norm_num) (by norm_num) hcut hev
  rw [hIp] at hlim
  linarith

end UpperTailOptimizers
