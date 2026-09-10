import UpperTailOptimizers.KRRS.Family
import UpperTailOptimizers.KRRS.BaseZero

/-!
# Appendix A: the compact-uniform Kenyon–Radin–Ren–Sadun theorem, from the KRR–S statements

This file is the final assembly of the rewritten Appendix A of `paper/bipodal_optimizer.tex`
(Appendix A).  It proves the master rectangle theorem `krrs_rectangle` and
the four public forms of `thm:krrs-analytic-extension` (`kenyonRadinRenSadun`,
`kenyonRadinRenSadunAnalytic`, `kenyonRadinRenSadunStrip`, `kenyonRadinRenSadunUniform`)
from **`KRRS/Inputs.lean` only** — i.e. from the two
transcribed KRR–S theorem statements `krrs_thm33` and `krrs_thm11` — rather than from the
three extracted assumptions of the former `KRRS/Axioms.lean`, which this derivation replaced
and which no longer exists (see the end of this docstring).

## The argument (Appendix A, paragraphs 2–4)

1. `krrs_thm33` gives `ζ_d`, `krrs_thm11` gives the KRR–S optimizer `O`.  The base point is
   `(ε₀, a₀, b₀, 0)` with `b₀ = ζ_d(ε₀)` and `a₀ = q₁₁⁰(ε₀)`; `b₀ ≠ ε₀`
   (`KRRSZeta.ne_self`), `b₀ ≠ (d-1)/d` (`KRRSZeta.ne_rStar`), and `b₀` maximises
   `ψ_d(ε₀,·)` (`KRRSZeta.isMax`).
2. `exists_C_chart` `eq:krrs-density-constraint` produces the pode-size chart `C` with its two
   windows `S`, `T`; `F1_base_zero` `eq:krrs-boundary-stationarity` gives `F₁(ε₀,a₀,b₀,0) = 0`;
   `exists_stationary_family` `eq:krrs-stationary-densities` then gives the two-sided analytic family
   `a_*`, `b_*` together with its local uniqueness.
3. The four parameter maps of the conclusion are
   `q₁₁ = a_*`, `q₁₂ = b_*`, `c = C(ε,a_*,b_*,ϑ)` `eq:krrs-block-size-map` and
   `q₂₂ = Q(ε,a_*,b_*,c)` `eq:krrs-large-block-map`.  All the "after shrinking" clauses of the
   appendix — interiority of the four parameters, `c < 1`, `b_*(ε,0) ≠ ε`, and analyticity
   at every point of the strip `|ϑ| < Δ` — are obtained from
   continuity/`AnalyticAt.eventually_analyticAt` at the base point followed by `exists_rect`.
4. **The identification** `eq:krrs-map-agreement`.  `exists_uniform_strip`
   `eq:krrs-uniform-domain` puts a whole rectangle `U × (0,Δ)` inside the KRR–S region.
   At `ε = ε₀` the one-sided limits `KRRSOptimizer.tendsto_q11/q12/q22/c` place the KRR–S
   parameters inside the two chart windows and the family window for all small `ϑ > 0`;
   fix one such `ϑ₁`.  Since the KRR–S parameters are analytic — hence continuous — on the
   region, the same holds on a full two-dimensional neighbourhood `𝒪` of `(ε₀, ϑ₁)`.  On
   `𝒪`, `F_eq_zero_of_maximizer` gives `F₁ = F₂ = 0`, the chart's uniqueness clause gives
   `c⁺ = C(ε,q₁₁⁺,q₁₂⁺,ϑ)`, and the family's uniqueness clause then gives
   `q₁₁⁺ = a_*`, `q₁₂⁺ = b_*`, whence also `c⁺ = c_*` and `q₂₂⁺ = q_*`.
5. **The identity theorem** extends that agreement from `𝒪` to all of `U × (0,Δ)`:
   both sides are real-analytic there and the rectangle is preconnected
   (`eqOn_prod_Ioo_of_eventuallyEq`).  This step is genuinely needed — the KRR–S limits of
   `KRRSOptimizer` are one-sided in `ϑ` at *fixed* `ε`, so the pinning argument alone
   produces no `ε`-uniform surplus window.

6. **The two boundary identifications.**  The paper's `q₁₂(ε,0) = ζ_d(ε)` and
   "`q₁₁(ε,0)` satisfies `S₀'(q₁₁) = 2S₀'(q₁₂) - S₀'(q₂₂)`" are recovered from step 5 and the
   one-sided KRR–S limits: on the slice `{ε} × (0,Δ)` the family equals the KRR–S parameter,
   the family is continuous at `(ε,0)` (it is analytic there), and `tendsto_q11`/`tendsto_q12`
   send the KRR–S parameter to `q₁₁⁰(ε)` / `ζ_d(ε)` as `ϑ ↘ 0`; uniqueness of limits along
   the `NeBot` filter `𝓝[>] 0` then pins `a_*(ε,0) = q₁₁⁰(ε)` and `b_*(ε,0) = ζ_d(ε)`.
   The conclusion does not *name* `ζ_d` or `q₁₁⁰` — it would then have to existentially
   quantify a `KRRSZeta d`, which every consumer would have to carry.  It states instead the
   two properties that define those values: `q₁₂(ε,0)` maximises `ψ_d(ε,·)` over
   `(0,1) ∖ {ε}` (`KRRSZeta.isMax`), and `S₀'(q₁₁(ε,0)) = 2S₀'(q₁₂(ε,0)) - S₀'(ε)`
   (`KRRSOptimizer.q110_rel`; `q₂₂(ε,0) = ε` is the neighbouring conjunct).  Since
   `ε ↦ q₁₂ ε 0` is analytic on `U` by clause 1, this is also the paper's remark that
   `thm:krrs-analytic-extension` implies `ζ_d` is real-analytic on `(0,1) ∖ {(d-1)/d}`; that reading is
   isolated as `zeta_analytic` at the end of the file.

Apart from those two extra boundary conjuncts and the strengthening of the analyticity clause
of `krrs_rectangle` from the slice `ϑ = 0` to the whole strip `|ϑ| < Δ`, the statements carried
over are character-for-character those of the previous derivation, which assumed `krrs_family`,
`krrs_stationarity` and `krrs_bipodal_near_constant` (the former `KRRS/Axioms.lean`, deleted
together with `KRRS/Localization.lean` when this derivation replaced it).
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

/-! ### The identity principle on an open rectangle -/

/-- **The identity principle on an open rectangle of `ℝ²`.**  Two real-analytic functions on
`(α,β) × (γ,δ)` that agree near one point of the rectangle agree on all of it: an open box
is convex, hence preconnected.

This is the appendix's "both sides are real-analytic on the connected set `U × (0,Δ)`; the
identity theorem for real-analytic functions therefore extends the equality to all of that
set" `eq:krrs-map-agreement`. -/
private theorem eqOn_prod_Ioo_of_eventuallyEq {f g : ℝ × ℝ → ℝ} {α β γ δ : ℝ}
    (hf : ∀ p ∈ Set.Ioo α β ×ˢ Set.Ioo γ δ, AnalyticAt ℝ f p)
    (hg : ∀ p ∈ Set.Ioo α β ×ˢ Set.Ioo γ δ, AnalyticAt ℝ g p)
    {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ Set.Ioo α β ×ˢ Set.Ioo γ δ) (h : f =ᶠ[𝓝 p₀] g) :
    Set.EqOn f g (Set.Ioo α β ×ˢ Set.Ioo γ δ) :=
  AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg
    ((convex_Ioo α β).prod (convex_Ioo γ δ)).isPreconnected hp₀ h

/-! ### The master rectangle theorem -/

/-- **The master rectangle theorem of Appendix A.**  Near a nonexceptional edge density
`ε₀` there are a window `U ∋ ε₀`, a surplus bound `Δ > 0`, and four functions of
`(ε, ϑ = τ - ε^m)` — real-analytic at every point of the two-sided strip
`{(ε, ϑ) : ε ∈ U, |ϑ| < Δ}` — such that on the
positive-surplus regime the entropy maximizer at `(ε, τ)` is the bipodal graphon with those
parameters, and is unique up to relabelling; at `ϑ = 0` the parameters take the degenerate
values `c = 0`, `q₂₂ = ε`, `q₁₂ = ζ_d(ε) ≠ ε`, `q₁₁ = q₁₁⁰(ε)`.

`ζ_d` and `q₁₁⁰` are named in `KRRS/Inputs.lean` but do not appear in the statement: the
boundary clause states instead the two properties that *define* them, so that a consumer
never has to produce a `KRRSZeta d` in order to use them.  Namely `q₁₂(ε,0)` maximises
`ψ_d(ε,·)` over `(0,1) ∖ {ε}` (this is `KRRSZeta.isMax`, and by uniqueness of the maximizer
it says `q₁₂(ε,0) = ζ_d(ε)`), and `q₁₁(ε,0)` satisfies the KRR–S boundary relation
`S₀'(q₁₁) = 2S₀'(q₁₂) - S₀'(ε)` (this is `KRRSOptimizer.q110_rel`).  Both are transported
from `ϑ > 0` by the one-sided KRR–S limits `tendsto_q11`/`tendsto_q12` and continuity of the
two-sided extension at `(ε,0)`.

All four public forms of `thm:krrs-analytic-extension` and `zeta_analytic` are immediate
corollaries. -/
theorem krrs_rectangle {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d)
    (hm : 2 ≤ H.edgeFinset.card) {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ), IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧
      (∀ ε ∈ U, ∀ ϑ : ℝ, |ϑ| < Δ →
        AnalyticAt ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (ε, ϑ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (ε, ϑ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (ε, ϑ) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => c p.1 p.2) (ε, ϑ)) ∧
      (∀ ε ∈ U, c ε 0 = 0 ∧ q22 ε 0 = ε ∧
        q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ≠ ε ∧
        (∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (q12 ε 0)) ∧
        dS0 (q11 ε 0) = 2 * dS0 (q12 ε 0) - dS0 ε) ∧
      (∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ H.edgeFinset.card →
        τ - ε ^ H.edgeFinset.card < Δ →
        q11 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        q12 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        q22 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        c ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Ioo (0:ℝ) 1 ∧
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ IsBipodal W ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2
            = bipodalValue (Set.Icc 0 (c ε (τ - ε ^ H.edgeFinset.card)))
                (q11 ε (τ - ε ^ H.edgeFinset.card))
                (q12 ε (τ - ε ^ H.edgeFinset.card))
                (q22 ε (τ - ε ^ H.edgeFinset.card)) z) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy ≤ W.entropy) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy = W.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2))) := by
  classical
  -- (1) the two KRR–S inputs, and the degenerate base point
  obtain ⟨Z⟩ := krrs_thm33 d hd
  obtain ⟨O⟩ := krrs_thm11 H hd hreg hm Z
  have hε₀I : ε₀ ∈ Set.Ioo (0:ℝ) 1 := ⟨hε₀0, hε₀1⟩
  set a₀ : ℝ := O.q110 ε₀ with ha₀def
  set b₀ : ℝ := Z.zeta ε₀ with hb₀def
  have ha₀I : a₀ ∈ Set.Ioo (0:ℝ) 1 := O.q110_mem ε₀ hε₀I hε₀
  have hb₀I : b₀ ∈ Set.Ioo (0:ℝ) 1 := Z.mem_Ioo ε₀ hε₀I
  have hb₀ε : b₀ ≠ ε₀ := Z.ne_self hd hε₀I hε₀
  have hb₀u : b₀ ≠ rStar d := Z.ne_rStar hε₀I hε₀
  have hmaxψ : ∀ w, 0 < w → w < 1 → w ≠ ε₀ → psiD d ε₀ w ≤ psiD d ε₀ b₀ :=
    fun w hw0 hw1 hwne => Z.isMax ε₀ hε₀I w ⟨hw0, hw1⟩ hwne
  -- (2) the pode-size chart (78)
  obtain ⟨Sc, Tc, C, hScopen, hScmem, hTcopen, hTcmem, hCana, -, hCcon, -, hCzeroS,
    hCzeroev, hCuniq⟩ := exists_C_chart H hd hreg hm hε₀0 hb₀I.1.le hb₀ε
  have hC000 : C ε₀ a₀ b₀ 0 = 0 := hCzeroev.self_of_nhds
  -- (3) (91) and the analytic family (95)
  have hF1base : F1 H d ε₀ a₀ b₀ 0 = 0 :=
    F1_base_zero H hd hreg hm O hε₀I hε₀ hScopen hScmem hTcopen hTcmem hCana hCcon hCuniq
  obtain ⟨Sb, r, astar, bstar, hSbopen, hSbmem, hr0, hastar0, hbstar0, hastarana,
    hbstarana, -, hbuniq⟩ :=
    exists_stationary_family H hd hreg hm hε₀0 hε₀1 ha₀I.1 ha₀I.2 hb₀I.1 hb₀I.2 hb₀ε hb₀u
      hmaxψ hCana hCzeroev hF1base
  -- (4) the two derived maps (96), (97), analytic at `(ε₀,0)`
  have hbaseval : ((fun w : ℝ × ℝ =>
      ((w.1, astar w.1 w.2, bstar w.1 w.2, w.2) : ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ))
      = ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    show ((ε₀, astar ε₀ 0, bstar ε₀ 0, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ)
      = ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ)
    rw [hastar0, hbstar0]
  have hPana : AnalyticAt ℝ (fun w : ℝ × ℝ =>
      ((w.1, astar w.1 w.2, bstar w.1 w.2, w.2) : ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ) :=
    analyticAt_fst.prod (hastarana.prod (hbstarana.prod analyticAt_snd))
  have hcana : AnalyticAt ℝ
      (fun w : ℝ × ℝ => C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2) ((ε₀, 0) : ℝ × ℝ) :=
    hCana.fun_comp_of_eq hPana hbaseval
  have hcval : C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0 = 0 := by rw [hastar0, hbstar0]; exact hC000
  have hbaseval2 : ((fun w : ℝ × ℝ =>
      ((w.1, astar w.1 w.2, bstar w.1 w.2, C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2) :
        ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ)) = ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ) := by
    show ((ε₀, astar ε₀ 0, bstar ε₀ 0, C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0) : ℝ × ℝ × ℝ × ℝ)
      = ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ)
    rw [hcval, hastar0, hbstar0]
  have hqana : AnalyticAt ℝ (fun w : ℝ × ℝ => Qmap w.1 (astar w.1 w.2) (bstar w.1 w.2)
      (C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)) ((ε₀, 0) : ℝ × ℝ) :=
    (analyticAt_Qmap (p := ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ)) (by norm_num)).fun_comp_of_eq
      (analyticAt_fst.prod (hastarana.prod (hbstarana.prod hcana))) hbaseval2
  have hqval : Qmap ε₀ (astar ε₀ 0) (bstar ε₀ 0) (C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0) = ε₀ := by
    rw [hcval, Qmap_zero]
  -- (5) all the "after shrinking" clauses, as one eventual statement at `(ε₀,0)`
  have hev4 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)),
      AnalyticAt ℝ (fun w : ℝ × ℝ => astar w.1 w.2) ((p.1, p.2) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => bstar w.1 w.2) ((p.1, p.2) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)
        ((p.1, p.2) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => Qmap w.1 (astar w.1 w.2) (bstar w.1 w.2)
        (C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)) ((p.1, p.2) : ℝ × ℝ) ∧
      astar p.1 p.2 ∈ Set.Ioo (0:ℝ) 1 ∧ bstar p.1 p.2 ∈ Set.Ioo (0:ℝ) 1 ∧
      ((p.1, astar p.1 p.2, bstar p.1 p.2, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Sc ∧
      C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2 < 1 ∧
      Qmap p.1 (astar p.1 p.2) (bstar p.1 p.2)
        (C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2) ∈ Set.Ioo (0:ℝ) 1 ∧
      bstar p.1 p.2 ≠ p.1 := by
    have e1 := hastarana.eventually_analyticAt
    have e2 := hbstarana.eventually_analyticAt
    have e3 := hcana.eventually_analyticAt
    have e4 := hqana.eventually_analyticAt
    have e5 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)), astar p.1 p.2 ∈ Set.Ioo (0:ℝ) 1 :=
      hastarana.continuousAt.eventually_mem
        (isOpen_Ioo.mem_nhds (by show astar ε₀ 0 ∈ Set.Ioo (0:ℝ) 1; rw [hastar0]; exact ha₀I))
    have e6 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)), bstar p.1 p.2 ∈ Set.Ioo (0:ℝ) 1 :=
      hbstarana.continuousAt.eventually_mem
        (isOpen_Ioo.mem_nhds (by show bstar ε₀ 0 ∈ Set.Ioo (0:ℝ) 1; rw [hbstar0]; exact hb₀I))
    have e7 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)),
        ((p.1, astar p.1 p.2, bstar p.1 p.2, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Sc := by
      have hc : ContinuousAt (fun p : ℝ × ℝ =>
          ((p.1, astar p.1 p.2, bstar p.1 p.2, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ)) ((ε₀, 0) : ℝ × ℝ) :=
        continuous_fst.continuousAt.prodMk (hastarana.continuousAt.prodMk
          (hbstarana.continuousAt.prodMk continuousAt_const))
      refine hc.eventually_mem (hScopen.mem_nhds ?_)
      show ((ε₀, astar ε₀ 0, bstar ε₀ 0, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Sc
      rw [hastar0, hbstar0]; exact hScmem
    have e8 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)),
        C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2 < 1 := by
      refine hcana.continuousAt.eventually_mem (Iio_mem_nhds ?_)
      show C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0 < 1
      rw [hcval]; norm_num
    have e9 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)),
        Qmap p.1 (astar p.1 p.2) (bstar p.1 p.2)
          (C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2) ∈ Set.Ioo (0:ℝ) 1 := by
      refine hqana.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds ?_)
      show Qmap ε₀ (astar ε₀ 0) (bstar ε₀ 0) (C ε₀ (astar ε₀ 0) (bstar ε₀ 0) 0)
        ∈ Set.Ioo (0:ℝ) 1
      rw [hqval]; exact hε₀I
    have e10 : ∀ᶠ p in 𝓝 ((ε₀ : ℝ), (0:ℝ)), bstar p.1 p.2 - p.1 ≠ 0 := by
      refine (hbstarana.continuousAt.sub continuous_fst.continuousAt).eventually_ne ?_
      show bstar ε₀ 0 - ε₀ ≠ 0
      rw [hbstar0]; exact sub_ne_zero.mpr hb₀ε
    filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] with
      p h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, sub_ne_zero.mp h10⟩
  obtain ⟨a₁, Δ₁, ha₁, hΔ₁, hrect⟩ := exists_rect (x₀ := ε₀)
    (P := fun x y =>
      AnalyticAt ℝ (fun w : ℝ × ℝ => astar w.1 w.2) ((x, y) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => bstar w.1 w.2) ((x, y) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)
        ((x, y) : ℝ × ℝ) ∧
      AnalyticAt ℝ (fun w : ℝ × ℝ => Qmap w.1 (astar w.1 w.2) (bstar w.1 w.2)
        (C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)) ((x, y) : ℝ × ℝ) ∧
      astar x y ∈ Set.Ioo (0:ℝ) 1 ∧ bstar x y ∈ Set.Ioo (0:ℝ) 1 ∧
      ((x, astar x y, bstar x y, (0:ℝ)) : ℝ × ℝ × ℝ × ℝ) ∈ Sc ∧
      C x (astar x y) (bstar x y) y < 1 ∧
      Qmap x (astar x y) (bstar x y) (C x (astar x y) (bstar x y) y) ∈ Set.Ioo (0:ℝ) 1 ∧
      bstar x y ≠ x) hev4
  -- (6) the uniform positive-surplus strip (100)
  obtain ⟨a₂, Δ₂, ha₂, hΔ₂, hstrip⟩ := exists_uniform_strip O hε₀I hε₀
  obtain ⟨a, hadef⟩ : ∃ t : ℝ, t = min (min a₁ a₂) r := ⟨_, rfl⟩
  obtain ⟨Δ, hΔdef⟩ : ∃ t : ℝ, t = min (min Δ₁ Δ₂) r := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [hadef]; exact lt_min (lt_min ha₁ ha₂) hr0
  have hΔ0 : 0 < Δ := by rw [hΔdef]; exact lt_min (lt_min hΔ₁ hΔ₂) hr0
  have ha1' : a ≤ a₁ := by rw [hadef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have ha2' : a ≤ a₂ := by rw [hadef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have har : a ≤ r := by rw [hadef]; exact min_le_right _ _
  have hΔ1' : Δ ≤ Δ₁ := by rw [hΔdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hΔ2' : Δ ≤ Δ₂ := by rw [hΔdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hΔr : Δ ≤ r := by rw [hΔdef]; exact min_le_right _ _
  -- (7) the four-dimensional window in which the pinning argument runs
  have hWev : ∀ᶠ w in 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ),
      w ∈ Sc ∧ w ∈ Tc ∧ w ∈ Sb ∧
      AnalyticAt ℝ (fun v : ℝ × ℝ × ℝ × ℝ => C v.1 v.2.1 v.2.2.1 v.2.2.2) w ∧
      partialC (fun v : ℝ × ℝ × ℝ × ℝ => That H v.1 v.2.1 v.2.2.1 v.2.2.2) w ≠ 0 ∧
      w.2.1 ∈ Set.Ioo (0:ℝ) 1 ∧ w.2.2.1 ∈ Set.Ioo (0:ℝ) 1 ∧ w.2.2.2 < 1 := by
    have f5 : ∀ᶠ w in 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ),
        partialC (fun v : ℝ × ℝ × ℝ × ℝ => That H v.1 v.2.1 v.2.2.1 v.2.2.2) w ≠ 0 :=
      eventually_partialC_That_ne_zero H hd hreg hm a₀ hε₀0 hb₀I.1.le hb₀ε
    have f6 : ∀ᶠ w in 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ), w.2.1 ∈ Set.Ioo (0:ℝ) 1 :=
      (continuous_fst.comp continuous_snd).continuousAt.eventually_mem
        (isOpen_Ioo.mem_nhds ha₀I)
    have f7 : ∀ᶠ w in 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ), w.2.2.1 ∈ Set.Ioo (0:ℝ) 1 :=
      (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt.eventually_mem
        (isOpen_Ioo.mem_nhds hb₀I)
    have f8 : ∀ᶠ w in 𝓝 ((ε₀, a₀, b₀, 0) : ℝ × ℝ × ℝ × ℝ), w.2.2.2 < 1 :=
      (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt.eventually_mem
        (Iio_mem_nhds (by norm_num))
    filter_upwards [hScopen.mem_nhds hScmem, hTcopen.mem_nhds hTcmem,
      hSbopen.mem_nhds hSbmem, hCana.eventually_analyticAt, f5, f6, f7, f8] with
      w h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨Wset, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hWev
  -- (8) the pinning argument: on the KRR–S region, inside `Wset`, the parameters agree
  have hpin : ∀ ε ϑ : ℝ, 0 < ϑ → ((ε, ϑ) : ℝ × ℝ) ∈ krrsRegion d O.hwin →
      ((ε, O.q11 ε ϑ, O.q12 ε ϑ, O.cpar ε ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ Wset →
      ((ε, O.q11 ε ϑ, O.q12 ε ϑ, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ Wset →
      O.q22 ε ϑ ∈ Set.Ioo (0:ℝ) 1 → |ε - ε₀| < r → |ϑ| < r →
      astar ε ϑ = O.q11 ε ϑ ∧ bstar ε ϑ = O.q12 ε ϑ ∧
        C ε (astar ε ϑ) (bstar ε ϑ) ϑ = O.cpar ε ϑ ∧
        Qmap ε (astar ε ϑ) (bstar ε ϑ) (C ε (astar ε ϑ) (bstar ε ϑ) ϑ) = O.q22 ε ϑ := by
    intro ε ϑ hϑ0 hmemR hWc hWt hq22 hεr hϑr
    obtain ⟨hSc1, -, -, -, hTcne1, h11a, h12a, hclt⟩ := hWsub hWc
    obtain ⟨-, hTc2, hSb2, hCana2, -, -, -, -⟩ := hWsub hWt
    obtain ⟨Wg, hWe, hWtd, hWae, hWmax, -⟩ := O.optimizer ((ε, ϑ) : ℝ × ℝ) hmemR
    obtain ⟨hI11, hI12, hI22, hIc⟩ := O.mem_Icc ((ε, ϑ) : ℝ × ℝ) hmemR
    -- the two constraints in block form
    have hae : ∀ᵐ z ∂gμ, Wg.toFun z.1 z.2
        = bipodalValue (Set.Icc 0
            ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta).2.2.2)
            ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta).1
            ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta).2.1
            ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta).2.2.1
            (id z.1, id z.2) := by
      filter_upwards [hWae] with z hz
      simpa using hz
    have htr := bipodal_transfer H
      (θ := ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta))
      hI11 hI12 hI22 hIc isRelabelling_id hae
    have hE : bipEdge ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta) = ε := by
      rw [← htr.1]; exact hWe
    have hTd : bipTd H ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta)
        = ε ^ H.edgeFinset.card + ϑ := by
      rw [← htr.2.1]; exact hWtd
    have hc1' : (1:ℝ) - O.cpar ε ϑ ≠ 0 := sub_ne_zero.mpr (ne_of_lt hclt).symm
    have hEexp : O.q11 ε ϑ * O.cpar ε ϑ ^ 2
        + O.q12 ε ϑ * (2 * O.cpar ε ϑ * (1 - O.cpar ε ϑ))
        + O.q22 ε ϑ * (1 - O.cpar ε ϑ) ^ 2 = ε := hE
    have hQq : Qmap ε (O.q11 ε ϑ) (O.q12 ε ϑ) (O.cpar ε ϑ) = O.q22 ε ϑ := by
      unfold Qmap
      rw [div_eq_iff (pow_ne_zero 2 hc1')]
      linear_combination (-1 : ℝ) * hEexp
    have hThat : That H ε (O.q11 ε ϑ) (O.q12 ε ϑ) (O.cpar ε ϑ)
        = ε ^ H.edgeFinset.card + ϑ := by
      rw [That_eq_bipTd, hQq]; exact hTd
    -- the chart's uniqueness clause pins the pode size
    have hCeq : O.cpar ε ϑ = C ε (O.q11 ε ϑ) (O.q12 ε ϑ) ϑ :=
      hCuniq ε (O.q11 ε ϑ) (O.q12 ε ϑ) (O.cpar ε ϑ) ϑ hSc1 hTc2 hThat
    -- stationarity of the KRR–S parameters
    have hFz := F_eq_zero_of_maximizer H hreg hTcopen hCcon hCuniq hCana2 hSc1 hTc2 hTcne1
      h11a h12a hq22 hIc.1 hclt hϑ0 hWe hWtd hWmax hWae
    have hE1 : F1 H d ε (O.q11 ε ϑ) (O.q12 ε ϑ) (C ε (O.q11 ε ϑ) (O.q12 ε ϑ) ϑ) = 0 := by
      rw [← hCeq]; exact hFz.1
    have hE2 : F2 H d ε (O.q11 ε ϑ) (O.q12 ε ϑ) (C ε (O.q11 ε ϑ) (O.q12 ε ϑ) ϑ) = 0 := by
      rw [← hCeq]; exact hFz.2
    obtain ⟨hq11e, hq12e⟩ :=
      hbuniq ε (O.q11 ε ϑ) (O.q12 ε ϑ) ϑ hSb2 hεr hϑr hE1 hE2
    refine ⟨hq11e.symm, hq12e.symm, ?_, ?_⟩
    · rw [← hq11e, ← hq12e, ← hCeq]
    · rw [← hq11e, ← hq12e, ← hCeq, hQq]
  -- (9) a point of the region over `ε₀` at which the pinning argument applies
  have hevϑ : ∀ᶠ ϑ in 𝓝[>] (0:ℝ),
      ((ε₀, O.q11 ε₀ ϑ, O.q12 ε₀ ϑ, O.cpar ε₀ ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ Wset ∧
      ((ε₀, O.q11 ε₀ ϑ, O.q12 ε₀ ϑ, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ Wset ∧
      O.q22 ε₀ ϑ ∈ Set.Ioo (0:ℝ) 1 ∧ ϑ < Δ ∧ 0 < ϑ := by
    have g1 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ),
        ((ε₀, O.q11 ε₀ ϑ, O.q12 ε₀ ϑ, O.cpar ε₀ ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ Wset :=
      (tendsto_krrsParams_c O hε₀I hε₀).eventually (hWopen.mem_nhds hWmem)
    have g2 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ),
        ((ε₀, O.q11 ε₀ ϑ, O.q12 ε₀ ϑ, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ Wset :=
      (tendsto_krrsParams_theta O hε₀I hε₀).eventually (hWopen.mem_nhds hWmem)
    have g3 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), O.q22 ε₀ ϑ ∈ Set.Ioo (0:ℝ) 1 :=
      (O.tendsto_q22 ε₀ hε₀I hε₀).eventually (isOpen_Ioo.mem_nhds hε₀I)
    have g4 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), ϑ < Δ :=
      Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hΔ0)
    have g5 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), 0 < ϑ := eventually_mem_nhdsWithin
    filter_upwards [g1, g2, g3, g4, g5] with ϑ h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ϑ₁, hϑ₁W, hϑ₁W', hϑ₁q22, hϑ₁Δ, hϑ₁0⟩ := hevϑ.exists
  have hmemR₁ : ((ε₀, ϑ₁) : ℝ × ℝ) ∈ krrsRegion d O.hwin :=
    hstrip ε₀ (by simpa using ha₂) ϑ₁ hϑ₁0 (lt_of_lt_of_le hϑ₁Δ hΔ2')
  -- (10) the pinning holds on a full two-dimensional neighbourhood of `(ε₀, ϑ₁)`
  obtain ⟨hana11, hana12, hana22, hanac⟩ := O.analytic ((ε₀, ϑ₁) : ℝ × ℝ) hmemR₁
  have hnbhd : ∀ᶠ p in 𝓝 ((ε₀, ϑ₁) : ℝ × ℝ),
      ((p.1, O.q11 p.1 p.2, O.q12 p.1 p.2, O.cpar p.1 p.2) : ℝ × ℝ × ℝ × ℝ) ∈ Wset ∧
      ((p.1, O.q11 p.1 p.2, O.q12 p.1 p.2, p.2) : ℝ × ℝ × ℝ × ℝ) ∈ Wset ∧
      O.q22 p.1 p.2 ∈ Set.Ioo (0:ℝ) 1 ∧
      p ∈ Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ := by
    have k1 : ∀ᶠ p in 𝓝 ((ε₀, ϑ₁) : ℝ × ℝ),
        ((p.1, O.q11 p.1 p.2, O.q12 p.1 p.2, O.cpar p.1 p.2) : ℝ × ℝ × ℝ × ℝ) ∈ Wset := by
      refine (continuous_fst.continuousAt.prodMk (hana11.continuousAt.prodMk
        (hana12.continuousAt.prodMk hanac.continuousAt))).eventually_mem
        (hWopen.mem_nhds ?_)
      exact hϑ₁W
    have k2 : ∀ᶠ p in 𝓝 ((ε₀, ϑ₁) : ℝ × ℝ),
        ((p.1, O.q11 p.1 p.2, O.q12 p.1 p.2, p.2) : ℝ × ℝ × ℝ × ℝ) ∈ Wset := by
      refine (continuous_fst.continuousAt.prodMk (hana11.continuousAt.prodMk
        (hana12.continuousAt.prodMk continuous_snd.continuousAt))).eventually_mem
        (hWopen.mem_nhds ?_)
      exact hϑ₁W'
    have k3 : ∀ᶠ p in 𝓝 ((ε₀, ϑ₁) : ℝ × ℝ), O.q22 p.1 p.2 ∈ Set.Ioo (0:ℝ) 1 :=
      hana22.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hϑ₁q22)
    have k4 : ∀ᶠ p in 𝓝 ((ε₀, ϑ₁) : ℝ × ℝ),
        p ∈ Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ :=
      (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨⟨by linarith, by linarith⟩, ⟨hϑ₁0, hϑ₁Δ⟩⟩
    filter_upwards [k1, k2, k3, k4] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  -- (11) the identity theorem (102)
  have hrectmem : ∀ p ∈ Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ,
      |p.1 - ε₀| < a₁ ∧ |p.2| < Δ₁ ∧ ((p.1, p.2) : ℝ × ℝ) ∈ krrsRegion d O.hwin ∧
      |p.1 - ε₀| < r ∧ |p.2| < r ∧ 0 < p.2 := by
    intro p hp
    obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
    have habs : |p.1 - ε₀| < a := abs_lt.mpr ⟨by linarith, by linarith⟩
    have habs2 : |p.2| < Δ := by rw [abs_of_pos hp3]; exact hp4
    exact ⟨lt_of_lt_of_le habs ha1', lt_of_lt_of_le habs2 hΔ1',
      hstrip p.1 (lt_of_lt_of_le habs ha2') p.2 hp3 (lt_of_lt_of_le hp4 hΔ2'),
      lt_of_lt_of_le habs har, lt_of_lt_of_le habs2 hΔr, hp3⟩
  have hagree : ∀ p ∈ Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ,
      astar p.1 p.2 = O.q11 p.1 p.2 ∧ bstar p.1 p.2 = O.q12 p.1 p.2 ∧
      C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2 = O.cpar p.1 p.2 ∧
      Qmap p.1 (astar p.1 p.2) (bstar p.1 p.2)
        (C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2) = O.q22 p.1 p.2 := by
    -- both sides are analytic on the rectangle …
    have hanaL : ∀ p ∈ Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ,
        AnalyticAt ℝ (fun w : ℝ × ℝ => astar w.1 w.2) p ∧
        AnalyticAt ℝ (fun w : ℝ × ℝ => bstar w.1 w.2) p ∧
        AnalyticAt ℝ (fun w : ℝ × ℝ => C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2) p ∧
        AnalyticAt ℝ (fun w : ℝ × ℝ => Qmap w.1 (astar w.1 w.2) (bstar w.1 w.2)
          (C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)) p := by
      intro p hp
      obtain ⟨hpa, hpΔ, -, -, -, -⟩ := hrectmem p hp
      obtain ⟨u1, u2, u3, u4, -, -, -, -, -, -⟩ := hrect p.1 hpa p.2 hpΔ
      exact ⟨u1, u2, u3, u4⟩
    have hanaR : ∀ p ∈ Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ,
        AnalyticAt ℝ (fun w : ℝ × ℝ => O.q11 w.1 w.2) p ∧
        AnalyticAt ℝ (fun w : ℝ × ℝ => O.q12 w.1 w.2) p ∧
        AnalyticAt ℝ (fun w : ℝ × ℝ => O.q22 w.1 w.2) p ∧
        AnalyticAt ℝ (fun w : ℝ × ℝ => O.cpar w.1 w.2) p := by
      intro p hp
      obtain ⟨-, -, hpR, -, -, -⟩ := hrectmem p hp
      exact O.analytic p hpR
    -- … and they agree near `(ε₀, ϑ₁)`
    have hp₁mem : ((ε₀, ϑ₁) : ℝ × ℝ) ∈ Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ :=
      ⟨⟨by linarith, by linarith⟩, ⟨hϑ₁0, hϑ₁Δ⟩⟩
    have hloc : ∀ᶠ p in 𝓝 ((ε₀, ϑ₁) : ℝ × ℝ),
        astar p.1 p.2 = O.q11 p.1 p.2 ∧ bstar p.1 p.2 = O.q12 p.1 p.2 ∧
        C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2 = O.cpar p.1 p.2 ∧
        Qmap p.1 (astar p.1 p.2) (bstar p.1 p.2)
          (C p.1 (astar p.1 p.2) (bstar p.1 p.2) p.2) = O.q22 p.1 p.2 := by
      filter_upwards [hnbhd] with p hp
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
      obtain ⟨-, -, hpR, hpr, hpr', hpos⟩ := hrectmem p hp4
      exact hpin p.1 p.2 hpos hpR hp1 hp2 hp3 hpr hpr'
    have E1 : Set.EqOn (fun w : ℝ × ℝ => astar w.1 w.2) (fun w : ℝ × ℝ => O.q11 w.1 w.2)
        (Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ) :=
      eqOn_prod_Ioo_of_eventuallyEq (fun p hp => (hanaL p hp).1) (fun p hp => (hanaR p hp).1)
        hp₁mem (by filter_upwards [hloc] with p hp using hp.1)
    have E2 : Set.EqOn (fun w : ℝ × ℝ => bstar w.1 w.2) (fun w : ℝ × ℝ => O.q12 w.1 w.2)
        (Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ) :=
      eqOn_prod_Ioo_of_eventuallyEq (fun p hp => (hanaL p hp).2.1)
        (fun p hp => (hanaR p hp).2.1) hp₁mem
        (by filter_upwards [hloc] with p hp using hp.2.1)
    have E3 : Set.EqOn
        (fun w : ℝ × ℝ => C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2)
        (fun w : ℝ × ℝ => O.cpar w.1 w.2)
        (Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ) :=
      eqOn_prod_Ioo_of_eventuallyEq (fun p hp => (hanaL p hp).2.2.1)
        (fun p hp => (hanaR p hp).2.2.2) hp₁mem
        (by filter_upwards [hloc] with p hp using hp.2.2.1)
    have E4 : Set.EqOn
        (fun w : ℝ × ℝ => Qmap w.1 (astar w.1 w.2) (bstar w.1 w.2)
          (C w.1 (astar w.1 w.2) (bstar w.1 w.2) w.2))
        (fun w : ℝ × ℝ => O.q22 w.1 w.2)
        (Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ) :=
      eqOn_prod_Ioo_of_eventuallyEq (fun p hp => (hanaL p hp).2.2.2)
        (fun p hp => (hanaR p hp).2.2.1) hp₁mem
        (by filter_upwards [hloc] with p hp using hp.2.2.2)
    exact fun p hp => ⟨E1 hp, E2 hp, E3 hp, E4 hp⟩
  -- (12) the conclusion
  refine ⟨Set.Ioo (ε₀ - a) (ε₀ + a), Δ, astar, bstar,
    (fun x y => Qmap x (astar x y) (bstar x y) (C x (astar x y) (bstar x y) y)),
    (fun x y => C x (astar x y) (bstar x y) y),
    isOpen_Ioo, ⟨by linarith, by linarith⟩, hΔ0, ?_, ?_, ?_⟩
  · -- analyticity on the whole strip `U × (-Δ, Δ)`, which is what `hrect` already gives
    intro ε hεU ϑ hϑ
    have hεa : |ε - ε₀| < a₁ :=
      lt_of_lt_of_le (abs_lt.mpr ⟨by linarith [hεU.1], by linarith [hεU.2]⟩) ha1'
    obtain ⟨u1, u2, u3, u4, -, -, -, -, -, -⟩ :=
      hrect ε hεa ϑ (lt_of_lt_of_le hϑ hΔ1')
    exact ⟨u1, u2, u4, u3⟩
  · -- the degenerate boundary values
    intro ε hεU
    have hεa : |ε - ε₀| < a₁ :=
      lt_of_lt_of_le (abs_lt.mpr ⟨by linarith [hεU.1], by linarith [hεU.2]⟩) ha1'
    obtain ⟨u1, u2, -, -, u5, u6, u7, -, -, u10⟩ :=
      hrect ε hεa 0 (by rw [abs_zero]; exact hΔ₁)
    have hC0 : C ε (astar ε 0) (bstar ε 0) 0 = 0 := hCzeroS ε (astar ε 0) (bstar ε 0) u7
    -- `ε` is a nonexceptional interior density: read it off the KRR–S region, which the
    -- rectangle meets over `ε`
    obtain ⟨hεI, hεne, -, -⟩ : ((ε, Δ / 2) : ℝ × ℝ) ∈ krrsRegion d O.hwin :=
      (hrectmem ((ε, Δ / 2) : ℝ × ℝ) ⟨hεU, ⟨by linarith, by linarith⟩⟩).2.2.1
    -- the family agrees with the KRR–S parameters on the punctured slice over `ε` …
    have hslice : ∀ᶠ ϑ in 𝓝[>] (0:ℝ),
        astar ε ϑ = O.q11 ε ϑ ∧ bstar ε ϑ = O.q12 ε ϑ := by
      have s1 : ∀ᶠ ϑ in 𝓝[>] (0:ℝ), ϑ < Δ :=
        Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hΔ0)
      filter_upwards [eventually_mem_nhdsWithin, s1] with ϑ h1 h2
      obtain ⟨g11, g12, -, -⟩ := hagree ((ε, ϑ) : ℝ × ℝ) ⟨hεU, ⟨h1, h2⟩⟩
      exact ⟨g11, g12⟩
    -- … so the one-sided KRR–S limits identify the two boundary values
    have hlim : ∀ f : ℝ → ℝ → ℝ, AnalyticAt ℝ (fun w : ℝ × ℝ => f w.1 w.2) ((ε, 0) : ℝ × ℝ) →
        ∀ g : ℝ → ℝ → ℝ, (∀ᶠ ϑ in 𝓝[>] (0:ℝ), f ε ϑ = g ε ϑ) →
        ∀ L : ℝ, Tendsto (fun ϑ => g ε ϑ) (𝓝[>] (0:ℝ)) (𝓝 L) → f ε 0 = L := by
      intro f hf g hfg L hL
      have hc : ContinuousAt (fun ϑ : ℝ => f ε ϑ) 0 :=
        ContinuousAt.comp (f := fun ϑ : ℝ => ((ε, ϑ) : ℝ × ℝ)) hf.continuousAt
          (continuousAt_const.prodMk continuousAt_id)
      have h1 : Tendsto (fun ϑ : ℝ => f ε ϑ) (𝓝[>] (0:ℝ)) (𝓝 (f ε 0)) :=
        Filter.Tendsto.mono_left hc nhdsWithin_le_nhds
      exact tendsto_nhds_unique (Filter.Tendsto.congr' hfg h1) hL
    have hb0 : bstar ε 0 = Z.zeta ε :=
      hlim bstar u2 O.q12 (by filter_upwards [hslice] with ϑ h using h.2) _
        (O.tendsto_q12 ε hεI hεne)
    have ha0' : astar ε 0 = O.q110 ε :=
      hlim astar u1 O.q11 (by filter_upwards [hslice] with ϑ h using h.1) _
        (O.tendsto_q11 ε hεI hεne)
    refine ⟨hC0, ?_, u5, u6, u10, ?_, ?_⟩
    · show Qmap ε (astar ε 0) (bstar ε 0) (C ε (astar ε 0) (bstar ε 0) 0) = ε
      rw [hC0, Qmap_zero]
    · -- `q₁₂(ε,0) = ζ_d(ε)` maximises `ψ_d(ε,·)` off the diagonal
      intro w hw hwne
      rw [hb0]
      exact Z.isMax ε hεI w hw hwne
    · -- the KRR–S boundary relation `S₀'(q₁₁) = 2S₀'(q₁₂) - S₀'(ε)`
      rw [ha0', hb0]
      exact O.q110_rel ε hεI hεne
  · -- the positive-surplus regime
    intro ε hεU τ hs0 hsΔ
    obtain ⟨ϑ, hϑdef⟩ : ∃ t : ℝ, t = τ - ε ^ H.edgeFinset.card := ⟨_, rfl⟩
    rw [← hϑdef]
    have hϑ0 : 0 < ϑ := by rw [hϑdef]; exact hs0
    have hϑΔ : ϑ < Δ := by rw [hϑdef]; exact hsΔ
    have hτ : ε ^ H.edgeFinset.card + ϑ = τ := by rw [hϑdef]; ring
    have hpmem : ((ε, ϑ) : ℝ × ℝ) ∈ Set.Ioo (ε₀ - a) (ε₀ + a) ×ˢ Set.Ioo (0:ℝ) Δ :=
      ⟨hεU, ⟨hϑ0, hϑΔ⟩⟩
    obtain ⟨hpa, hpΔ, hpR, -, -, -⟩ := hrectmem ((ε, ϑ) : ℝ × ℝ) hpmem
    obtain ⟨-, -, -, -, u5, u6, -, u8, u9, -⟩ :=
      hrect ε hpa ϑ hpΔ
    obtain ⟨g11, g12, gc, g22⟩ :
        astar ε ϑ = O.q11 ε ϑ ∧ bstar ε ϑ = O.q12 ε ϑ ∧
        C ε (astar ε ϑ) (bstar ε ϑ) ϑ = O.cpar ε ϑ ∧
        Qmap ε (astar ε ϑ) (bstar ε ϑ) (C ε (astar ε ϑ) (bstar ε ϑ) ϑ) = O.q22 ε ϑ :=
      hagree ((ε, ϑ) : ℝ × ℝ) hpmem
    obtain ⟨Wg, hWe, hWtd, hWae, hWmax, hWuniq⟩ := O.optimizer ((ε, ϑ) : ℝ × ℝ) hpR
    obtain ⟨hI11, hI12, hI22, hIc⟩ := O.mem_Icc ((ε, ϑ) : ℝ × ℝ) hpR
    -- `0 < c`: a null first pode makes the graphon constant, killing the surplus
    have hcpos : 0 < C ε (astar ε ϑ) (bstar ε ϑ) ϑ := by
      rcases lt_or_eq_of_le hIc.1 with h | h
      · rw [gc]; exact h
      · exfalso
        have hc00 : O.cpar ε ϑ = 0 := h.symm
        have hae : ∀ᵐ z ∂gμ, Wg.toFun z.1 z.2
            = bipodalValue (Set.Icc 0
                ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta).2.2.2)
                ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta).1
                ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta).2.1
                ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta).2.2.1
                (id z.1, id z.2) := by
          filter_upwards [hWae] with z hz
          simpa using hz
        have htr := bipodal_transfer H
          (θ := ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta))
          hI11 hI12 hI22 hIc isRelabelling_id hae
        have hE : bipEdge ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta) = ε := by
          rw [← htr.1]; exact hWe
        have hTd : bipTd H ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta)
            = ε ^ H.edgeFinset.card + ϑ := by
          rw [← htr.2.1]; exact hWtd
        have hqE : bipEdge ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta)
            = O.q22 ε ϑ := by simp [bipEdge, hc00]
        have hq22ε : O.q22 ε ϑ = ε := by rw [← hqE]; exact hE
        have hTq : bipTd H ((O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ, O.cpar ε ϑ) : Theta)
            = O.q22 ε ϑ ^ H.edgeFinset.card := by
          show tBip H (O.q11 ε ϑ) (O.q12 ε ϑ) (O.q22 ε ϑ) (O.cpar ε ϑ) = _
          rw [hc00, tBip_zero]
        rw [hTq, hq22ε] at hTd
        linarith
    refine ⟨u5, u6, u9, ⟨hcpos, u8⟩, Wg, hWe, by rw [hWtd, hτ], ?_, ?_, ?_, ?_⟩
    · exact ⟨Set.Icc 0 (O.cpar ε ϑ), O.q11 ε ϑ, O.q12 ε ϑ, O.q22 ε ϑ,
        measurableSet_Icc, hI11, hI12, hI22, hWae⟩
    · filter_upwards [hWae] with z hz
      rw [hz, g22, gc, g11, g12]
    · intro W' h1 h2
      exact hWmax W' h1 (by rw [h2, ← hτ])
    · intro W' h1 h2 h3
      exact hWuniq W' h1 (by rw [h2, ← hτ]) h3

/-! ### The public forms of `thm:krrs-analytic-extension` -/

/-- **`thm:krrs-analytic-extension`**, proved in Appendix A style from the two
transcribed KRR–S theorem statements of `KRRS/Inputs.lean`.

Away from the exceptional density `(d-1)/d`, the entropy maximizer at fixed edge density
`ε` and fixed `H`-density `τ = ε^m + δ` (small `δ > 0`) exists, is bipodal, and is unique up
to relabelling: any other maximizer `W'` equals `W` relabelled by a measure-preserving
transformation `σ` of `[0,1]`.

(Kenyon–Radin–Ren–Sadun, arXiv:1509.05370, `thm:krrs-bipodality`; the compact-uniform organisation is
Appendix A of `paper/bipodal_optimizer.tex`.) -/
theorem kenyonRadinRenSadun {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ : ℝ), IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧
      ∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ (H.edgeFinset.card) →
        τ - ε ^ (H.edgeFinset.card) < Δ →
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ IsBipodal W ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy ≤ W.entropy) ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy = W.entropy →
            ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
              ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) := by
  obtain ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0, -, -, hmain⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  refine ⟨U, Δ, hUopen, hε₀U, hΔ0, fun ε hε τ h1 h2 => ?_⟩
  obtain ⟨-, -, -, -, W, hWe, hWt, hWbip, -, hWmax, hWuniq⟩ := hmain ε hε τ h1 h2
  exact ⟨W, hWe, hWt, hWbip, hWmax, hWuniq⟩

/-- **`thm:krrs-analytic-extension`, analytic-parametrization clause**, proved in
`krrs_rectangle` above from the two transcribed KRR–S theorem statements and the
analytic inverse function theorem (Appendix A of `paper/bipodal_optimizer.tex`).

The bipodal parameters `(q₁₁, q₁₂, q₂₂, c)` of the fixed-`(e, t_H)` entropy maximizer are
jointly real-analytic in `(ε, δ)` at the degenerate boundary `δ = 0`, with degenerate values
`c(ε,0) = 0`, `q₂₂(ε,0) = ε`, `q₁₂(ε,0) = ζ_d(ε) ≠ ε` and `q₁₁(ε,0) = q₁₁⁰(ε)`, all block
densities being interior there.  The last two equalities are stated as the defining
properties rather than by naming `ζ_d`, `q₁₁⁰`: `q₁₂(ε,0)` maximises `ψ_d(ε,·)` over
`(0,1) ∖ {ε}`, and `S₀'(q₁₁(ε,0)) = 2S₀'(q₁₂(ε,0)) - S₀'(ε)`.  See `krrs_rectangle`.
Analyticity is stated here only on the boundary slice `δ = 0`, which is what the consumers
use; `kenyonRadinRenSadunStrip` below carries the paper's full strip `U × (−Δ, Δ)`.
On `0 < δ < Δ` the concrete two-block graphon with these
parameters and block `A = [0,c]` is an entropy maximizer at `(e, t_H) = (ε, τ)`.  The
paper's clause `c(ε,δ) = O(δ)` is not restated here: analyticity and `c(ε,0) = 0` give it
*locally* uniformly in `ε`, but `\Cref{thm:krrs-analytic-extension}` asks for it uniformly on `U`.  That form is
`kenyonRadinRenSadunUniform` below, which carries every clause of this theorem together with a
single constant, on a possibly smaller rectangle. -/
theorem kenyonRadinRenSadunAnalytic {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ), IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧
      (∀ ε ∈ U,
        AnalyticAt ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => c p.1 p.2) (ε, 0)) ∧
      (∀ ε ∈ U, c ε 0 = 0 ∧ q22 ε 0 = ε ∧
        q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ≠ ε ∧
        (∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (q12 ε 0)) ∧
        dS0 (q11 ε 0) = 2 * dS0 (q12 ε 0) - dS0 ε) ∧
      (∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ (H.edgeFinset.card) →
        τ - ε ^ (H.edgeFinset.card) < Δ →
        q11 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        q12 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        q22 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        c ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy ≤ W.entropy) ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2
            = bipodalValue (Set.Icc 0 (c ε (τ - ε ^ H.edgeFinset.card)))
                (q11 ε (τ - ε ^ H.edgeFinset.card))
                (q12 ε (τ - ε ^ H.edgeFinset.card))
                (q22 ε (τ - ε ^ H.edgeFinset.card)) z)) := by
  obtain ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0, hana, hbdry, hmain⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  refine ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0,
    fun ε hε => hana ε hε 0 (by rw [abs_zero]; exact hΔ0), hbdry, fun ε hε τ h1 h2 => ?_⟩
  obtain ⟨g11, g12, g22, gc, W, hWe, hWt, -, hWae, hWmax, -⟩ := hmain ε hε τ h1 h2
  exact ⟨Set.Ioo_subset_Icc_self g11, Set.Ioo_subset_Icc_self g12,
    Set.Ioo_subset_Icc_self g22, Set.Ioo_subset_Icc_self gc, W, hWe, hWt, hWmax, hWae⟩

/-- **`thm:krrs-analytic-extension`, the two-sided continuation as the paper states it.**

`thm:krrs-analytic-extension` asserts that the parameter map "extends real-analytically to `U × (−Δ, Δ)`", and
that extension *is* what the theorem adds to Kenyon–Radin–Ren–Sadun, who define the map only
for `ϑ > 0`.  The paper needs it because the later analysis differentiates the map and
Taylor-expands it at the boundary `ϑ = 0`.

`kenyonRadinRenSadunAnalytic` states the analyticity only on the boundary slice `U × {0}`,
which is all its consumers use.  This is the strip, on the same `U` and `Δ` those two theorems
take from `krrs_rectangle`: analyticity at *every* point of `U × (−Δ, Δ)`, which is
`AnalyticOnNhd ℝ · (U ×ˢ Set.Ioo (-Δ) Δ)` written pointwise.

For `ϑ < 0` the values are only the analytic continuation — as `paper/bipodal_optimizer.tex` says
immediately after the theorem, they describe no entropy maximizer, and nothing here claims
they do — this theorem states no maximizer clause at all.  The positive-surplus maximizer is
`kenyonRadinRenSadun` / `kenyonRadinRenSadunAnalytic`, built from the same `krrs_rectangle`
witnesses `U` and `Δ`. -/
theorem kenyonRadinRenSadunStrip {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ), IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => c p.1 p.2) (U ×ˢ Set.Ioo (-Δ) Δ) ∧
      (∀ ε ∈ U, c ε 0 = 0 ∧ q22 ε 0 = ε ∧
        q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ≠ ε ∧
        (∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (q12 ε 0)) ∧
        dS0 (q11 ε 0) = 2 * dS0 (q12 ε 0) - dS0 ε) := by
  obtain ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0, hana, hbdry, -⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  have habs : ∀ p : ℝ × ℝ, p ∈ U ×ˢ Set.Ioo (-Δ) Δ → p.1 ∈ U ∧ |p.2| < Δ := by
    rintro ⟨ε, ϑ⟩ ⟨hε, hϑ1, hϑ2⟩
    exact ⟨hε, abs_lt.mpr ⟨hϑ1, hϑ2⟩⟩
  exact ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0,
    fun p hp => (hana p.1 (habs p hp).1 p.2 (habs p hp).2).1,
    fun p hp => (hana p.1 (habs p hp).1 p.2 (habs p hp).2).2.1,
    fun p hp => (hana p.1 (habs p hp).1 p.2 (habs p hp).2).2.2.1,
    fun p hp => (hana p.1 (habs p hp).1 p.2 (habs p hp).2).2.2.2,
    hbdry⟩

/-! ## The uniform `c = O(ϑ)` clause

`\Cref{thm:krrs-analytic-extension}` asserts `c(ε,ϑ) = O(ϑ)` as `ϑ ↓ 0` **uniformly for `ε ∈ U`**.  Analyticity
together with `c(ε,0) = 0` gives this only *locally* uniformly, which is why the clause was
long left unstated.  But the theorem is free to shrink `U`, and after shrinking to a ball whose
closure sits inside the analytic region the bound is genuinely uniform: `fderiv c` is analytic
there, hence continuous, hence bounded on the compact closed ball, and the mean value
inequality along the segment from `(ε,0)` to `(ε,ϑ)` — which stays in the ball, the ball being
convex — turns that bound into `|c(ε,ϑ)| ≤ C|ϑ|`. -/

/-- **An analytic function vanishing on a horizontal slice is uniformly `O` of the second
coordinate.**  This is the shrinking argument, isolated from the KRR–S setting. -/
theorem exists_uniform_linear_bound {f : ℝ × ℝ → ℝ} {x₀ : ℝ}
    (hf : AnalyticAt ℝ f (x₀, 0)) (hzero : ∀ᶠ x in nhds x₀, f (x, 0) = 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ x y : ℝ, |x - x₀| < r → |y| < r → |f (x, y)| ≤ C * |y| := by
  -- a ball on which `f` is analytic at every point
  obtain ⟨r₁, hr₁0, hr₁⟩ :=
    Metric.mem_nhds_iff.mp (hf.eventually_analyticAt)
  -- a ball on which the slice vanishes
  obtain ⟨r₂, hr₂0, hr₂⟩ := Metric.mem_nhds_iff.mp hzero
  obtain ⟨r, hrdef⟩ : ∃ t : ℝ, t = min (r₁ / 2) (r₂ / 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; exact lt_min (by linarith) (by linarith)
  have hrr₁ : r < r₁ := by rw [hrdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrr₂ : r < r₂ := by rw [hrdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨S, hSdef⟩ : ∃ T : Set (ℝ × ℝ), T = Metric.closedBall ((x₀, 0) : ℝ × ℝ) r := ⟨_, rfl⟩
  have hSsub : S ⊆ Metric.ball ((x₀, 0) : ℝ × ℝ) r₁ := by
    rw [hSdef]
    exact fun p hp => Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hp) hrr₁)
  have hana : AnalyticOnNhd ℝ f (Metric.ball ((x₀, 0) : ℝ × ℝ) r₁) := fun p hp => hr₁ hp
  -- `fderiv f` is analytic, hence continuous, on the same ball
  have hfd : AnalyticOnNhd ℝ (fderiv ℝ f) (Metric.ball ((x₀, 0) : ℝ × ℝ) r₁) :=
    hana.fderiv_of_isOpen Metric.isOpen_ball
  have hcont : ContinuousOn (fderiv ℝ f) S :=
    (hfd.continuousOn).mono hSsub
  obtain ⟨C₀, hC₀⟩ := (by rw [hSdef]; exact isCompact_closedBall _ _ : IsCompact S)
    |>.exists_bound_of_continuousOn hcont
  obtain ⟨C, hCdef⟩ : ∃ t : ℝ, t = max C₀ 1 := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hCdef]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨r, C, hr0, hC0, fun x y hx hy => ?_⟩
  -- the two endpoints of the segment lie in `S`
  have hmem0 : ((x, 0) : ℝ × ℝ) ∈ S := by
    rw [hSdef, Metric.mem_closedBall, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero, abs_zero]
    exact max_le hx.le (by linarith [abs_nonneg (x - x₀)])
  have hmemy : ((x, y) : ℝ × ℝ) ∈ S := by
    rw [hSdef, Metric.mem_closedBall, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_le hx.le hy.le
  -- the slice vanishes at `x`
  have hslice : f (x, 0) = 0 := by
    refine hr₂ (Metric.mem_ball.mpr ?_)
    rw [Real.dist_eq]
    exact lt_trans hx hrr₂
  -- the mean value inequality on the convex ball
  have hdiff : ∀ p ∈ S, DifferentiableAt ℝ f p := fun p hp => (hana p (hSsub hp)).differentiableAt
  have hbound : ∀ p ∈ S, ‖fderiv ℝ f p‖ ≤ C := fun p hp =>
    le_trans (hC₀ p hp) (by rw [hCdef]; exact le_max_left _ _)
  have hconv : Convex ℝ S := by rw [hSdef]; exact convex_closedBall _ _
  have hmv := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hmem0 hmemy
  have hnorm : ‖((x, y) : ℝ × ℝ) - ((x, 0) : ℝ × ℝ)‖ = |y| := by
    rw [Prod.norm_def]
    simp
  rw [hslice, sub_zero, Real.norm_eq_abs, hnorm] at hmv
  exact hmv

/-- **`thm:krrs-analytic-extension`, full form.**

`kenyonRadinRenSadunAnalytic` together with the paper's uniform smallness clause

`c(ε,ϑ) = O(ϑ)  (ϑ ↓ 0),  uniformly for ε ∈ U`,

on a possibly smaller rectangle.  `\Cref{thm:krrs-analytic-extension}` asks for uniformity over the whole of `U`,
not merely local uniformity, and analyticity alone does not give that — but the theorem chooses
`U`, so shrinking it to a ball with compact closure inside the analytic region is free, and
`exists_uniform_linear_bound` then supplies a single constant.  Every other clause is of the
form `∀ ε ∈ U, …` or `∀ ε ∈ U, ∀ τ, … < Δ → …`, so all of them survive the shrinking. -/
theorem kenyonRadinRenSadunUniform {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (Δ C : ℝ) (q11 q12 q22 c : ℝ → ℝ → ℝ),
      IsOpen U ∧ ε₀ ∈ U ∧ 0 < Δ ∧ 0 < C ∧
      (∀ ε ∈ U,
        AnalyticAt ℝ (fun p : ℝ × ℝ => q11 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q12 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => q22 p.1 p.2) (ε, 0) ∧
        AnalyticAt ℝ (fun p : ℝ × ℝ => c p.1 p.2) (ε, 0)) ∧
      (∀ ε ∈ U, c ε 0 = 0 ∧ q22 ε 0 = ε ∧
        q11 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ∈ Set.Ioo (0:ℝ) 1 ∧ q12 ε 0 ≠ ε ∧
        (∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (q12 ε 0)) ∧
        dS0 (q11 ε 0) = 2 * dS0 (q12 ε 0) - dS0 ε) ∧
      (∀ ε ∈ U, ∀ ϑ : ℝ, 0 ≤ ϑ → ϑ < Δ → |c ε ϑ| ≤ C * ϑ) ∧
      (∀ ε ∈ U, ∀ τ : ℝ, 0 < τ - ε ^ (H.edgeFinset.card) →
        τ - ε ^ (H.edgeFinset.card) < Δ →
        q11 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        q12 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        q22 ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        c ε (τ - ε ^ H.edgeFinset.card) ∈ Set.Icc (0:ℝ) 1 ∧
        ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
          (∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ →
            W'.entropy ≤ W.entropy) ∧
          (∀ᵐ z ∂gμ, W.toFun z.1 z.2
            = bipodalValue (Set.Icc 0 (c ε (τ - ε ^ H.edgeFinset.card)))
                (q11 ε (τ - ε ^ H.edgeFinset.card))
                (q12 ε (τ - ε ^ H.edgeFinset.card))
                (q22 ε (τ - ε ^ H.edgeFinset.card)) z)) := by
  obtain ⟨U₀, Δ₀, q11, q12, q22, c, hU₀open, hε₀U₀, hΔ₀0, hana, hbdry, hmain⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  -- the shrinking argument, applied to `c`
  have hzero : ∀ᶠ x in nhds ε₀, (fun p : ℝ × ℝ => c p.1 p.2) (x, 0) = 0 :=
    Filter.eventually_of_mem (hU₀open.mem_nhds hε₀U₀) fun x hx => (hbdry x hx).1
  obtain ⟨r, C, hr0, hC0, hlin⟩ :=
    exists_uniform_linear_bound (f := fun p : ℝ × ℝ => c p.1 p.2)
      (hana ε₀ hε₀U₀ 0 (by rw [abs_zero]; exact hΔ₀0)).2.2.2 hzero
  refine ⟨U₀ ∩ Metric.ball ε₀ r, min Δ₀ r, C, q11, q12, q22, c,
    hU₀open.inter Metric.isOpen_ball, ⟨hε₀U₀, Metric.mem_ball_self hr0⟩,
    lt_min hΔ₀0 hr0, hC0,
    fun ε hε => hana ε hε.1 0 (by rw [abs_zero]; exact hΔ₀0),
    fun ε hε => hbdry ε hε.1, ?_, ?_⟩
  · intro ε hε ϑ hϑ0 hϑΔ
    have hx : |ε - ε₀| < r := by
      have := Metric.mem_ball.mp hε.2
      rwa [Real.dist_eq] at this
    have hy : |ϑ| < r := by
      rw [abs_of_nonneg hϑ0]
      exact lt_of_lt_of_le hϑΔ (min_le_right _ _)
    have := hlin ε ϑ hx hy
    rwa [abs_of_nonneg hϑ0] at this
  · intro ε hε τ h1 h2
    obtain ⟨g11, g12, g22, gc, W, hWe, hWt, -, hWae, hWmax, -⟩ :=
      hmain ε hε.1 τ h1 (lt_of_lt_of_le h2 (min_le_left _ _))
    exact ⟨Set.Ioo_subset_Icc_self g11, Set.Ioo_subset_Icc_self g12,
      Set.Ioo_subset_Icc_self g22, Set.Ioo_subset_Icc_self gc, W, hWe, hWt, hWmax, hWae⟩

/-! ### Real-analyticity of `ζ_d` -/

/-- **`ζ_d` is real-analytic on `(0,1) ∖ {(d-1)/d}`.**  This is `paper/bipodal_optimizer.tex`'s remark
that "\Cref{thm:krrs-analytic-extension} below also implies that `ζ_d` is real-analytic on
`(0,1) ∖ {(d-1)/d}`", read off `krrs_rectangle`: the boundary value `ε ↦ q₁₂(ε,0)` is
analytic (restrict the joint analyticity at `(ε,0)` to the horizontal slice) and it has the
defining property of `ζ_d(ε)` — it lies in `(0,1)`, differs from `ε`, and maximises
`ψ_d(ε,·)` off the diagonal.

As with `KRRSZeta.isMax`, the guard `w ≠ ε` is Lean's, not the paper's: `psiD d ε ε` is the
junk value `0/0 = 0` rather than the honest limit.

The selector produced here is *the* `ζ_d`: `KRRSZeta.isMax` gives `psiD d ε (zeta ε) ≤
psiD d ε (Z.zeta ε)` and the clause below gives the reverse, so the two agree wherever the
maximizer is unique — the KRR–S result recorded at `thm:krrs-cross-density` and the
paragraph following it. -/
theorem zeta_analytic {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, H.degree v = d) (hm : 2 ≤ H.edgeFinset.card)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₀ : ε₀ ≠ rStar d) :
    ∃ (U : Set ℝ) (zeta : ℝ → ℝ), IsOpen U ∧ ε₀ ∈ U ∧
      ∀ ε ∈ U, AnalyticAt ℝ zeta ε ∧ zeta ε ∈ Set.Ioo (0:ℝ) 1 ∧ zeta ε ≠ ε ∧
        ∀ w ∈ Set.Ioo (0:ℝ) 1, w ≠ ε → psiD d ε w ≤ psiD d ε (zeta ε) := by
  obtain ⟨U, Δ, q11, q12, q22, c, hUopen, hε₀U, hΔ0, hana, hbdry, -⟩ :=
    krrs_rectangle H hd hreg hm hε₀0 hε₀1 hε₀
  refine ⟨U, fun ε => q12 ε 0, hUopen, hε₀U, fun ε hε => ?_⟩
  obtain ⟨-, -, -, h12, hne, hmax, -⟩ := hbdry ε hε
  exact ⟨(hana ε hε 0 (by rw [abs_zero]; exact hΔ0)).2.1.fun_comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl,
    h12, hne, hmax⟩

end UpperTailOptimizers
