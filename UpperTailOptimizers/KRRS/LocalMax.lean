import UpperTailOptimizers.KRRS.Reduced

/-!
# From graphon maximality to a finite-dimensional local maximum

Paragraph 4 of Appendix A of `paper/bipodal_optimizer.tex` (Appendix A) argues:

> All sufficiently small variations of `(a,b)`, with `c` and `q` supplied by `C` and `Q`,
> remain admissible bipodal graphons with the same two constraints.  Local maximality
> therefore gives `F₁ = F₂ = 0`.

This file formalises the *first* half of that sentence — the bridge from the graphon layer
to the finite-dimensional one.  It turns the statement "`W` maximises the entropy among all
graphons with edge density `ε` and `H`-density `ε^m + ϑ`, and `W` is (up to relabelling) the
bipodal graphon with parameters `(a, b, Q(ε,a,b,c), c)`, `c = C(ε,a,b,ϑ)`" into

  `IsLocalMax (fun p => Ŝ(ε, p.1, p.2, C(ε, p.1, p.2, ϑ))) (a, b)`,

the local maximality of the reduced entropy `Σ(ε,·,·,ϑ)` of `eq:krrs-constrained-entropy`.
The step from there to the vanishing of the two partial derivatives `F₁`, `F₂` is the
elementary calculus fact `partials_eq_zero_of_isLocalMax` at the end of the file.

## Contents

* `isLocalMax_reduced_entropy` — **paragraph 4** (and the identical argument in paragraph
  3): graphon maximality transports to `IsLocalMax` of the reduced entropy.
* `partials_eq_zero_of_isLocalMax` — the two partial derivatives of a function of two real
  variables vanish at a local maximum; the calculus half of "local maximality therefore
  gives `F₁ = F₂ = 0`".

The competitor construction that supplies the admissible variations — for `(a,b,c)` with
`a, b, Q(ε,a,b,c) ∈ [0,1]` and `0 ≤ c < 1`, a genuine graphon realising `ε`, `𝒯̂(ε,a,b,c)`
and `Ŝ(ε,a,b,c)` — is file-private: only `isLocalMax_reduced_entropy` uses it.
-/

namespace UpperTailOptimizers

open MeasureTheory Filter Topology

/-! ### The bipodal competitor -/

/-- **The competitor of Appendix A, paragraph 4.**  Given `(ε, a, b, c)` with the three
block densities `a`, `b`, `Q(ε,a,b,c)` in `[0,1]` and a pode size `0 ≤ c < 1`, the bipodal
graphon `G(a, b, Q(ε,a,b,c), c)` is admissible and realises the reduced functionals:

* its edge density is exactly `ε` — this is the defining property `bipEdge_Qmap` of
  `Q` `eq:krrs-edge-constraint`;
* its `H`-density is `𝒯̂(ε,a,b,c)` (`That_eq_bipTd`);
* its entropy is `Ŝ(ε,a,b,c)` (`Shat_eq_bipEnt`).

The hypothesis `c < 1` (rather than `c ≤ 1`) is what makes `Q` meaningful: it is the
nonvanishing of the denominator `(1-c)²` of `eq:krrs-edge-constraint`. -/
private theorem exists_bipodal_competitor {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V)
    [DecidableRel H.Adj] {ε a b c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hq : Qmap ε a b c ∈ Set.Icc (0:ℝ) 1) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = That H ε a b c ∧
      W.entropy = Shat ε a b c := by
  refine ⟨bipG ((a, b, Qmap ε a b c, c) : Theta) ha hb hq, ?_, ?_, ?_⟩
  · rw [bipG_edgeDensity ha hb hq hc0 hc1.le]
    exact bipEdge_Qmap (ne_of_lt hc1)
  · rw [bipG_tDensity H ha hb hq hc0 hc1.le, That_eq_bipTd]
  · rw [bipG_entropy ha hb hq hc0 hc1.le, Shat_eq_bipEnt]

/-! ### Graphon maximality becomes a finite-dimensional local maximum -/

/-- **Appendix A, paragraph 4 (and the same argument in paragraph 3).**  A graphon `W` that
maximises the entropy at `(ε, ε^m + ϑ)` and is, up to a measure-preserving relabelling `σ`,
the bipodal graphon with parameters `(a, b, Q(ε,a,b,c), c)` where `c = C(ε,a,b,ϑ)`, makes
`(a,b)` a local maximizer of the reduced entropy

  `Σ(ε, a, b, ϑ) = Ŝ(ε, a, b, C(ε,a,b,ϑ))`   `eq:krrs-constrained-entropy`.

The proof is the appendix's: the centre value `Σ(ε,a,b,ϑ)` *is* `s(W)` by `bipodal_transfer`
and `Shat_eq_bipEnt`; every nearby `(a',b')` yields, via `exists_bipodal_competitor`, an
admissible competitor with the same two constraints — the `H`-density constraint being
`hconstraint`, i.e. the defining property `eq:krrs-density-constraint` of the chart `C` — and
`hWmax` applied to it is precisely `Σ(ε,a',b',ϑ) ≤ Σ(ε,a,b,ϑ)`.

The openness of the chart window `T` and the continuity of `C` are what let the
neighbourhood be shrunk so that all of `a'`, `b'`, `c'` and `q'` stay in `(0,1)`. -/
theorem isLocalMax_reduced_entropy {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {T : Set (ℝ × ℝ × ℝ × ℝ)}
    {C : ℝ → ℝ → ℝ → ℝ → ℝ} {ε a b ϑ : ℝ}
    (hTopen : IsOpen T)
    (hconstraint : ∀ ε a b ϑ : ℝ, ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T →
      That H ε a b (C ε a b ϑ) = ε ^ H.edgeFinset.card + ϑ)
    (hCcont : ContinuousAt (fun w : ℝ × ℝ × ℝ × ℝ => C w.1 w.2.1 w.2.2.1 w.2.2.2)
      ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ))
    (hmemT : ((ε, a, b, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T)
    (ha : a ∈ Set.Ioo (0:ℝ) 1) (hb : b ∈ Set.Ioo (0:ℝ) 1)
    (hq : Qmap ε a b (C ε a b ϑ) ∈ Set.Ioo (0:ℝ) 1)
    (hc : C ε a b ϑ ∈ Set.Ioo (0:ℝ) 1)
    {W : Graphon}
    (hWmax : ∀ W' : Graphon, W'.edgeDensity = ε →
      W'.tDensity H = ε ^ H.edgeFinset.card + ϑ → W'.entropy ≤ W.entropy)
    {σ : ℝ → ℝ} (hσ : IsRelabelling σ)
    (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2
      = bipodalValue (Set.Icc 0 (C ε a b ϑ)) a b (Qmap ε a b (C ε a b ϑ)) (σ z.1, σ z.2)) :
    IsLocalMax (fun p : ℝ × ℝ => Shat ε p.1 p.2 (C ε p.1 p.2 ϑ)) (a, b) := by
  classical
  -- Step 1: the value of the reduced entropy at the centre is `s(W)`.
  have hcentre : Shat ε a b (C ε a b ϑ) = W.entropy := by
    have h11 : ((a, b, Qmap ε a b (C ε a b ϑ), C ε a b ϑ) : Theta).1 ∈ Set.Icc (0:ℝ) 1 :=
      Set.Ioo_subset_Icc_self ha
    have h12 : ((a, b, Qmap ε a b (C ε a b ϑ), C ε a b ϑ) : Theta).2.1 ∈ Set.Icc (0:ℝ) 1 :=
      Set.Ioo_subset_Icc_self hb
    have h22 : ((a, b, Qmap ε a b (C ε a b ϑ), C ε a b ϑ) : Theta).2.2.1
        ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hq
    have hcI : ((a, b, Qmap ε a b (C ε a b ϑ), C ε a b ϑ) : Theta).2.2.2
        ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hc
    have htr := bipodal_transfer H
      (θ := ((a, b, Qmap ε a b (C ε a b ϑ), C ε a b ϑ) : Theta)) h11 h12 h22 hcI hσ hae
    rw [Shat_eq_bipEnt, htr.2.2]
  -- Step 2: shrink the neighbourhood so that the chart data stay admissible.
  have hins : Continuous (fun p : ℝ × ℝ => ((ε, p.1, p.2, ϑ) : ℝ × ℝ × ℝ × ℝ)) := by
    fun_prop
  have hCat : ContinuousAt (fun p : ℝ × ℝ => C ε p.1 p.2 ϑ) ((a, b) : ℝ × ℝ) := by
    exact hCcont.comp (x := ((a, b) : ℝ × ℝ))
      (f := fun p : ℝ × ℝ => ((ε, p.1, p.2, ϑ) : ℝ × ℝ × ℝ × ℝ)) hins.continuousAt
  have hQat : ContinuousAt (fun p : ℝ × ℝ => Qmap ε p.1 p.2 (C ε p.1 p.2 ϑ))
      ((a, b) : ℝ × ℝ) := by
    have hQ : ContinuousAt (fun w : ℝ × ℝ × ℝ × ℝ => Qmap w.1 w.2.1 w.2.2.1 w.2.2.2)
        ((ε, a, b, C ε a b ϑ) : ℝ × ℝ × ℝ × ℝ) :=
      (analyticAt_Qmap (p := ((ε, a, b, C ε a b ϑ) : ℝ × ℝ × ℝ × ℝ))
        (ne_of_lt hc.2)).continuousAt
    exact hQ.comp (f := fun p : ℝ × ℝ => ((ε, p.1, p.2, C ε p.1 p.2 ϑ) : ℝ × ℝ × ℝ × ℝ))
      (continuousAt_const.prodMk (continuousAt_fst.prodMk (continuousAt_snd.prodMk hCat)))
  have hTev : ∀ᶠ p in 𝓝 ((a, b) : ℝ × ℝ), ((ε, p.1, p.2, ϑ) : ℝ × ℝ × ℝ × ℝ) ∈ T :=
    hins.continuousAt.eventually_mem (hTopen.mem_nhds hmemT)
  have haev : ∀ᶠ p in 𝓝 ((a, b) : ℝ × ℝ), p.1 ∈ Set.Ioo (0:ℝ) 1 :=
    continuousAt_fst.eventually_mem (isOpen_Ioo.mem_nhds ha)
  have hbev : ∀ᶠ p in 𝓝 ((a, b) : ℝ × ℝ), p.2 ∈ Set.Ioo (0:ℝ) 1 :=
    continuousAt_snd.eventually_mem (isOpen_Ioo.mem_nhds hb)
  have hcev : ∀ᶠ p in 𝓝 ((a, b) : ℝ × ℝ), C ε p.1 p.2 ϑ ∈ Set.Ioo (0:ℝ) 1 :=
    hCat.eventually_mem (isOpen_Ioo.mem_nhds hc)
  have hqev : ∀ᶠ p in 𝓝 ((a, b) : ℝ × ℝ),
      Qmap ε p.1 p.2 (C ε p.1 p.2 ϑ) ∈ Set.Ioo (0:ℝ) 1 :=
    hQat.eventually_mem (isOpen_Ioo.mem_nhds hq)
  -- Step 3: on that neighbourhood, compare with the bipodal competitor.
  filter_upwards [hTev, haev, hbev, hcev, hqev] with p hpT hpa hpb hpc hpq
  obtain ⟨W', hW'e, hW't, hW's⟩ :=
    exists_bipodal_competitor H (Set.Ioo_subset_Icc_self hpa) (Set.Ioo_subset_Icc_self hpb)
      (Set.Ioo_subset_Icc_self hpq) hpc.1.le hpc.2
  have hW'tc : W'.tDensity H = ε ^ H.edgeFinset.card + ϑ := by
    rw [hW't]; exact hconstraint ε p.1 p.2 ϑ hpT
  have hle := hWmax W' hW'e hW'tc
  rw [hW's] at hle
  rw [hcentre]
  exact hle

/-! ### The calculus step -/

/-- **The two partial derivatives vanish at a local maximum.**  This is the elementary
half of "local maximality therefore gives `F₁ = F₂ = 0`" in paragraph 4 of Appendix A:
restrict the two-dimensional local maximum to the two coordinate lines through `(a,b)` and
apply `IsLocalMax.hasDerivAt_eq_zero` on each. -/
theorem partials_eq_zero_of_isLocalMax {f : ℝ × ℝ → ℝ} {a b : ℝ} {u v : ℝ}
    (h : IsLocalMax f (a, b))
    (hu : HasDerivAt (fun x => f (x, b)) u a)
    (hv : HasDerivAt (fun y => f (a, y)) v b) : u = 0 ∧ v = 0 := by
  have hlineu : ContinuousAt (fun x : ℝ => ((x, b) : ℝ × ℝ)) a := by fun_prop
  have hlinev : ContinuousAt (fun y : ℝ => ((a, y) : ℝ × ℝ)) b := by fun_prop
  have hmaxu : IsLocalMax (fun x : ℝ => f (x, b)) a := hlineu.tendsto.eventually h
  have hmaxv : IsLocalMax (fun y : ℝ => f (a, y)) b := hlinev.tendsto.eventually h
  exact ⟨hmaxu.hasDerivAt_eq_zero hu, hmaxv.hasDerivAt_eq_zero hv⟩

end UpperTailOptimizers
