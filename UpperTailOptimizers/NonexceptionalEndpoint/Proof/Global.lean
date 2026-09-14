import UpperTailOptimizers.NonexceptionalEndpoint.Proof.Main
import UpperTailOptimizers.NonexceptionalEndpoint.LocalReduction.Global

/-!
# Theorems 4.1 and 1.5 in the paper's form

`local_structure` in `NonexceptionalEndpoint/Proof/Main.lean` proves the global optimizer theorem,
including the positive analytic coefficient and the analytic bipodal family, with one window per
field.  `nonexceptional_endpoint` states `thm:nonexceptional-endpoint` of `paper/paper.tex` as the
paper does: one pair `ρ, η` whose set
`U = {(p,r) : |p - pc(r)| < η, |r - r₀| < ρ}` is an open neighbourhood of `(pc(r₀), r₀)`, on which
every conclusion holds.  `nonexceptional_optimizers` is `thm:nonexceptional-optimizers`, obtained
by taking this `U`.  `main_bipodal_optimizer` is the projection of `local_structure` onto
`NonexceptionalOptimizers`.
-/

namespace UpperTailOptimizers

open Filter Topology

/-- **Theorem 1.5**, field form: a direct projection of `local_structure`. -/
theorem main_bipodal_optimizer {d : ℕ} (hd : 2 ≤ d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1) (hr₀ex : r₀ ≠ rStar d) : NonexceptionalOptimizers H d r₀ :=
  (local_structure hd H hreg hm hr₀0 hr₀1 hr₀ex).toNonexceptionalOptimizers

/-- **`thm:nonexceptional-endpoint`.**  Let `H` be `d`-regular, `d ≥ 2`, and
`r₀ ∈ (0,1) \ {r_*}`.  There are `ρ, η > 0` such that
`U = {(p,r) : |p - pc(r)| < η, |r - r₀| < ρ}` is an open neighbourhood of `(pc(r₀), r₀)`, and
functions `c, q₁₁, q₁₂, q₂₂` and a constant `C` such that for `(p,r) ∈ U` with `p < pc(r)`:

* the minimizer is unique up to relabelling, nonconstant and bipodal; it equals a.e. the bipodal
  graphon with smaller block `[0, c(p,r)]`, `c(p,r) ∈ (0,1/2)`, and densities
  `q₁₁(p,r), q₁₂(p,r), q₂₂(p,r)` within the smaller block, across, and within the larger block;
* `c, q₁₁, q₁₂, q₂₂` are real-analytic at `(p,r)`;
* every optimizer `W` has `|e(W) - (r - λ/A_H(r))| ≤ Cλ²`, and
  `|Φ_H(p,r) - (J_p(r) - λ²/(2A_H(r)))| ≤ Cλ³`, with `λ = λ(p,r)`;

for every `r` with `|r - r₀| < ρ`, `c(p,r) → 0` as `p ↑ pc(r)`; and `A_H` is positive and
real-analytic on `(0,1) \ {r_*}`. -/
theorem nonexceptional_endpoint {d : ℕ} (hd : 2 ≤ d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1) (hr₀ex : r₀ ≠ rStar d) :
    ∃ ρ η : ℝ, 0 < ρ ∧ 0 < η ∧
      IsOpen {q : ℝ × ℝ | |q.1 - pcGlobal d q.2| < η ∧ |q.2 - r₀| < ρ} ∧
      |pcGlobal d r₀ - pcGlobal d r₀| < η ∧ |r₀ - r₀| < ρ ∧
      ∃ (c q11 q12 q22 : ℝ → ℝ → ℝ) (C : ℝ), 0 ≤ C ∧
        (∀ r : ℝ, |r - r₀| < ρ → ∀ p : ℝ, |p - pcGlobal d r| < η → p < pcGlobal d r →
          (∃ Wstar : Graphon, Feasible H r Wstar ∧ Wstar.Ip p = phiVar H p r ∧
            IsBipodal Wstar ∧ (¬ ∃ a : ℝ, ∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2 = a) ∧
            (∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2
              = bipodalValue (Set.Icc 0 (c p r)) (q11 p r) (q12 p r) (q22 p r) z) ∧
            ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) ∧
          c p r ∈ Set.Ioo (0:ℝ) (1 / 2) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => c q.1 q.2) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q11 q.1 q.2) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q12 q.1 q.2) (p, r) ∧
          AnalyticAt ℝ (fun q : ℝ × ℝ => q22 q.1 q.2) (p, r) ∧
          (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
            |W.edgeDensity - (r - lambdaGlobal d p r / AHGlobal H d r)|
              ≤ C * lambdaGlobal d p r ^ 2) ∧
          |phiVar H p r - (Jp p r - lambdaGlobal d p r ^ 2 / (2 * AHGlobal H d r))|
            ≤ C * lambdaGlobal d p r ^ 3) ∧
        (∀ r : ℝ, |r - r₀| < ρ → Tendsto (fun p => c p r) (𝓝[<] (pcGlobal d r)) (𝓝 0)) ∧
        ∀ r : ℝ, 0 < r → r < 1 → r ≠ rStar d →
          AnalyticAt ℝ (AHGlobal H d) r ∧ 0 < AHGlobal H d r := by
  obtain ⟨M, hrU, hrne⟩ := lz_boundary_arcs hd hr₀0 hr₀1 hr₀ex
  obtain ⟨ρ, η, L, Cd, hρ, hη, -, hCd, Dl, q11, q12, q22, cc, hbase, hfamily⟩ :=
    bipodal_family_smallBlock hd M H hreg hm hrU hrne
  set m := H.edgeFinset.card
  -- the open window: `pc` is continuous on `|r - r₀| < ρ ⊆ (0,1)`
  have hopen : IsOpen {q : ℝ × ℝ | |q.1 - pcGlobal d q.2| < η ∧ |q.2 - r₀| < ρ} := by
    have hs : IsOpen {q : ℝ × ℝ | |q.2 - r₀| < ρ} :=
      isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const)) continuous_const
    have hf : ContinuousOn (fun q : ℝ × ℝ => q.1 - pcGlobal d q.2) {q | |q.2 - r₀| < ρ} := by
      refine continuousOn_fst.sub ((continuousOn_pcGlobal hd).comp continuousOn_snd ?_)
      intro q hq
      exact ⟨(hbase q.2 hq).2.2.1, (hbase q.2 hq).2.2.2.1⟩
    have h := hf.isOpen_inter_preimage hs (isOpen_Ioo (a := -η) (b := η))
    convert h using 1
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo, abs_lt]
    tauto
  refine ⟨ρ, η, hρ, hη, hopen, by simpa using hη, by simpa using hρ,
    fun p r => cc (r - Dl (p, r)) (r ^ m - (r - Dl (p, r)) ^ m),
    fun p r => q11 (r - Dl (p, r)) (r ^ m - (r - Dl (p, r)) ^ m),
    fun p r => q12 (r - Dl (p, r)) (r ^ m - (r - Dl (p, r)) ^ m),
    fun p r => q22 (r - Dl (p, r)) (r ^ m - (r - Dl (p, r)) ^ m), Cd, hCd,
    fun r hr p hpη hp => ?_, fun r hr => ?_,
    fun r hr0 hr1 hrex => analyticAt_AHGlobal_and_pos hd H hreg hm hr0 hr1 hrex⟩
  · have hrU' : r ∈ M.U := (hbase r hr).1
    have hp_lo : M.pc r - η < p := by
      rw [← pcGlobal_eq_pc hd M hrU']; linarith [(abs_lt.mp hpη).1]
    have hp_hi : p < M.pc r := by rwa [← pcGlobal_eq_pc hd M hrU']
    obtain ⟨-, -, -, -, -, -, -, -, h11, h12, h22, hc, hedge, ⟨Wstar, hWf, hWo, hWb, hWnc, hWu⟩,
      hDl, -, hΦ, ε, θ, hε, hθ, -, -, -, hcc, -, -, -, -, B, hBf, hBo, -, -, hBae⟩ :=
      hfamily r hr p hp_lo hp_hi
    rw [AH_eq_AHGlobal H hd M hrU', lambdaDisp_eq_lambdaGlobal hd M hrU'] at hDl hΦ
    subst hε hθ
    refine ⟨⟨B, hBf, hBo, ?_, ?_, hBae, fun W hWf' hWo' => ?_⟩, hcc, hc, h11, h12, h22,
      fun W hWf' hWo' => ?_, hΦ⟩
    · -- `B` is a relabelling of the bipodal nonconstant optimizer `Wstar`
      obtain ⟨σ, hσ, hBσ⟩ := hWu B hBf hBo
      exact isBipodal_of_relabel hσ hWb hBσ
    · rintro ⟨a, ha⟩
      obtain ⟨σ, hσ, hBσ⟩ := hWu B hBf hBo
      refine hWnc ⟨a, ?_⟩
      obtain ⟨τ, hτ, hτW⟩ := exists_relabel_symm hσ hBσ
      have hq := (hτ.measurePreserving.prod hτ.measurePreserving).quasiMeasurePreserving
      filter_upwards [hτW, hq.ae ha] with z hz hza
      rw [hz]; exact hza
    · obtain ⟨σ, hσ, hWσ⟩ := hWu W hWf' hWo'
      obtain ⟨τ, hτ, hBτ⟩ := hWu B hBf hBo
      obtain ⟨τ', hτ', hτ'B⟩ := exists_relabel_symm hτ hBτ
      exact ⟨fun x => τ' (σ x), hτ'.comp hσ, ae_relabel_trans hσ.measurePreserving hWσ hτ'B⟩
    · rw [hedge W hWf' hWo', show r - Dl (p, r) - (r - lambdaGlobal d p r / AHGlobal H d r)
        = -(Dl (p, r) - lambdaGlobal d p r / AHGlobal H d r) by ring, abs_neg]
      exact hDl
  · have hrU' : r ∈ M.U := (hbase r hr).1
    rw [pcGlobal_eq_pc hd M hrU']
    exact (hbase r hr).2.2.2.2.2.2.2.2.2.2

/-- **`thm:nonexceptional-optimizers`.**  Let `H` be `d`-regular, `d ≥ 2`, and
`r₀ ∈ (0,1) \ {r_*}`.  There is an open neighbourhood `U` of `(pc(r₀), r₀)` and a block-size
function `c` such that for `(p,r) ∈ U` with `p < pc(r)` the minimizer is unique up to relabelling,
nonconstant and bipodal, with smaller block `[0, c(p,r)]`; for every `r` with `(pc(r), r) ∈ U`,
`c(p,r) → 0` as `p ↑ pc(r)`; the optimizers satisfy both expansions with one constant; and
`A_H` is positive and analytic on `(0,1) \ {r_*}`. -/
theorem nonexceptional_optimizers {d : ℕ} (hd : 2 ≤ d)
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = d) (hm : 1 ≤ H.edgeFinset.card)
    {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1) (hr₀ex : r₀ ≠ rStar d) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (pcGlobal d r₀, r₀) ∈ U ∧
      ∃ (c q11 q12 q22 : ℝ → ℝ → ℝ) (C : ℝ), 0 ≤ C ∧
        (∀ p r : ℝ, (p, r) ∈ U → p < pcGlobal d r →
          (∃ Wstar : Graphon, Feasible H r Wstar ∧ Wstar.Ip p = phiVar H p r ∧
            IsBipodal Wstar ∧ (¬ ∃ a : ℝ, ∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2 = a) ∧
            (∀ᵐ z ∂gμ, Wstar.toFun z.1 z.2
              = bipodalValue (Set.Icc 0 (c p r)) (q11 p r) (q12 p r) (q22 p r) z) ∧
            ∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
              ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
                ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = Wstar.toFun (σ z.1) (σ z.2)) ∧
          c p r ∈ Set.Ioo (0:ℝ) (1 / 2) ∧
          (∀ W : Graphon, Feasible H r W → W.Ip p = phiVar H p r →
            |W.edgeDensity - (r - lambdaGlobal d p r / AHGlobal H d r)|
              ≤ C * lambdaGlobal d p r ^ 2) ∧
          |phiVar H p r - (Jp p r - lambdaGlobal d p r ^ 2 / (2 * AHGlobal H d r))|
            ≤ C * lambdaGlobal d p r ^ 3) ∧
        (∀ r : ℝ, (pcGlobal d r, r) ∈ U →
          Tendsto (fun p => c p r) (𝓝[<] (pcGlobal d r)) (𝓝 0)) ∧
        ∀ r : ℝ, 0 < r → r < 1 → r ≠ rStar d →
          AnalyticAt ℝ (AHGlobal H d) r ∧ 0 < AHGlobal H d r := by
  obtain ⟨ρ, η, -, -, hopen, hη₀, hρ₀, c, q11, q12, q22, C, hC, hwin, hlim, hcoef⟩ :=
    nonexceptional_endpoint hd H hreg hm hr₀0 hr₀1 hr₀ex
  refine ⟨_, hopen, ⟨hη₀, hρ₀⟩, c, q11, q12, q22, C, hC, fun p r hU hp => ?_,
    fun r hU => hlim r hU.2, hcoef⟩
  obtain ⟨hopt, hc, -, -, -, -, hedge, hΦ⟩ := hwin r hU.2 p hU.1 hp
  exact ⟨hopt, hc, hedge, hΦ⟩

end UpperTailOptimizers
