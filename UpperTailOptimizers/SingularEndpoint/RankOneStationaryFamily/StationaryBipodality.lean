import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.StationaryReduction
import UpperTailOptimizers.SingularEndpoint.RankOneStationaryFamily.CdfTransport
import UpperTailOptimizers.Preliminaries.Graphons.BipodalBridge

/-!
# `lem:stationary-rank-one-bipodality` in the paper's form

`stationary_rank_one_two_values` (`SingularEndpoint/RankOneStationaryFamily/StationaryReduction.lean`) proves that a
stationary rank-one factor with pointwise bounds `η ≤ f ≤ 1-η` takes at most two values up to
null sets.  `lem:stationary-rank-one-bipodality` of `paper/paper.tex` assumes the bounds only
almost everywhere, assumes that `f` is not a.e. constant, and concludes the normal form: there
are `α ∈ (0,1)` and `0 < s < t < 1` such that, after a measure-preserving relabelling,
`f = f_{α,s,t} = s 1_{[0,α]} + t 1_{(α,1]}` almost everywhere.  `stationary_rank_one_bipodality`
states it in that form.

## Proof

The KKT conditions depend only on the a.e. class of the graphon
(`isStationary_congr_ae`, from `SymKernel.Ip_congr_ae` and `SymKernel.tDensity_congr_ae`), so
`f` may be replaced by a measurable `g = f` a.e. with pointwise bounds.  The two values `s < t`
of `g` both have positive measure because `f` is not a.e. constant, and both lie in
`[η, 1-η]`.  With `A = [0,1] ∩ {g = s}` and `α = |A|`, `relabel A` carries `A` onto `[0,α]`
almost everywhere (`relabel_mem_Icc_iff_mem_ae`), so `f = f_{α,s,t} ∘ relabel A` a.e.; the inverse
relabelling turns this into `f ∘ τ = f_{α,s,t}` a.e.
-/

namespace UpperTailOptimizers

namespace SingularEndpoint

open MeasureTheory Filter

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`t(H,·)` on kernels depends only on the a.e. class.**  The kernel form of
`tDensity_congr_ae`. -/
theorem SymKernel.tDensity_congr_ae {w w' : SymKernel} (H : SimpleGraph V) [DecidableRel H.Adj]
    (hae : ∀ᵐ z ∂gμ, w.toFun z.1 z.2 = w'.toFun z.1 z.2) :
    w.tDensity H = w'.tDensity H := by
  have hedge : ∀ e ∈ H.edgeFinset, ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      Sym2.lift ⟨fun a b => w.toFun (x a) (x b), fun a b => w.symm' (x a) (x b)⟩ e
        = Sym2.lift ⟨fun a b => w'.toFun (x a) (x b), fun a b => w'.symm' (x a) (x b)⟩ e := by
    refine Sym2.ind (fun a b => ?_)
    intro he
    have hadj : H.Adj a b := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hpe := (measurePreserving_pair (V := V) hadj.ne).quasiMeasurePreserving.ae_eq hae
    filter_upwards [hpe] with x hx; exact hx
  have hall := (Filter.eventually_all_finset _).mpr hedge
  have hprod : ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      (∏ e ∈ H.edgeFinset, Sym2.lift
          ⟨fun a b => w.toFun (x a) (x b), fun a b => w.symm' (x a) (x b)⟩ e)
        = ∏ e ∈ H.edgeFinset, Sym2.lift
          ⟨fun a b => w'.toFun (x a) (x b), fun a b => w'.symm' (x a) (x b)⟩ e := by
    filter_upwards [hall] with x hx
    exact Finset.prod_congr rfl (fun e he => hx e he)
  unfold SymKernel.tDensity
  exact integral_congr_ae hprod

/-- **`I_p` on kernels depends only on the a.e. class.** -/
theorem SymKernel.Ip_congr_ae {w w' : SymKernel} (p : ℝ)
    (hae : ∀ᵐ z ∂gμ, w.toFun z.1 z.2 = w'.toFun z.1 z.2) : w.Ip p = w'.Ip p := by
  unfold SymKernel.Ip
  refine integral_congr_ae ?_
  filter_upwards [hae] with z hz
  rw [hz]

/-- **Stationarity depends only on the a.e. class of the graphon.**  For every direction `U`
and every `ε`, the perturbed kernels `W + εU` and `W' + εU` agree almost everywhere, so the two
functionals of `ε` in `eq:graphon-stationarity` coincide. -/
theorem isStationary_congr_ae {W W' : Graphon} (H : SimpleGraph V) [DecidableRel H.Adj]
    {p μ : ℝ} (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W'.toFun z.1 z.2)
    (h : IsStationary H p μ W) : IsStationary H p μ W' := by
  intro U
  have hfun : (fun ε : ℝ => ((graphonKernel W').pert U ε).Ip p
        - μ * ((graphonKernel W').pert U ε).tDensity H)
      = fun ε : ℝ => ((graphonKernel W).pert U ε).Ip p
        - μ * ((graphonKernel W).pert U ε).tDensity H := by
    funext ε
    have hp : ∀ᵐ z ∂gμ, ((graphonKernel W').pert U ε).toFun z.1 z.2
        = ((graphonKernel W).pert U ε).toFun z.1 z.2 := by
      filter_upwards [hae] with z hz
      show W'.toFun z.1 z.2 + ε * U.toFun z.1 z.2 = W.toFun z.1 z.2 + ε * U.toFun z.1 z.2
      rw [hz]
    rw [SymKernel.Ip_congr_ae p hp, SymKernel.tDensity_congr_ae H hp]
  rw [hfun]
  exact h U

/-- **`lem:stationary-rank-one-bipodality` (bipodality of stationary rank-one graphons).**  Let
`p ∈ (0,1)` and let `f` be measurable with values in `[0,1]` and, for some `η > 0`,
`η ≤ f ≤ 1-η` almost everywhere.  If `f ⊗ f` satisfies the KKT conditions at `(p,r)` with
multiplier `μ` and `f` is not a.e. constant, then there are `α ∈ (0,1)` and `0 < s < t < 1`
such that, after a measure-preserving relabelling `σ`,
`f = f_{α,s,t} = s 1_{[0,α]} + t 1_{(α,1]}` almost everywhere.

The paper also assumes `r ∈ (0,1)`; the proof does not use it.  `μ ≥ 0` is part of
`SatisfiesKKT`. -/
theorem stationary_rank_one_bipodality (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : ∀ v, H.degree v = d) {p r μ η : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (hη : 0 < η) (hfη : ∀ᵐ y ∂unitμ, η ≤ f y ∧ f y ≤ 1 - η)
    (hkkt : SatisfiesKKT H p r μ (rankOneGraphon hfm hf0 hf1))
    (hnc : ¬ ∃ c : ℝ, ∀ᵐ y ∂unitμ, f y = c) :
    ∃ α s t : ℝ, α ∈ Set.Ioo (0:ℝ) 1 ∧ 0 < s ∧ s < t ∧ t < 1 ∧
      ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
        ∀ᵐ x ∂unitμ, f (σ x)
          = (Set.Icc 0 α).indicator (fun _ => s) x + (Set.Ioc α 1).indicator (fun _ => t) x := by
  classical
  -- ### A pointwise-interior representative `g` of `f`
  obtain ⟨y₀, hy₀⟩ := hfη.exists
  have hη1 : η ≤ 1 - η := le_trans hy₀.1 hy₀.2
  set S : Set ℝ := {y | η ≤ f y ∧ f y ≤ 1 - η} with hSdef
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const hfm).inter (measurableSet_le hfm measurable_const)
  set g : ℝ → ℝ := S.piecewise f (fun _ => η) with hgdef
  have hgm : Measurable g := Measurable.piecewise hSm hfm measurable_const
  have hg0 : ∀ y, η ≤ g y := by
    intro y
    by_cases hy : y ∈ S
    · rw [hgdef, Set.piecewise_eq_of_mem _ _ _ hy]; exact hy.1
    · rw [hgdef, Set.piecewise_eq_of_notMem _ _ _ hy]
  have hg1 : ∀ y, g y ≤ 1 - η := by
    intro y
    by_cases hy : y ∈ S
    · rw [hgdef, Set.piecewise_eq_of_mem _ _ _ hy]; exact hy.2
    · rw [hgdef, Set.piecewise_eq_of_notMem _ _ _ hy]; exact hη1
  have hfg : ∀ᵐ y ∂unitμ, f y = g y := by
    filter_upwards [hfη] with y hy
    rw [hgdef, Set.piecewise_eq_of_mem _ _ _ (show y ∈ S from hy)]
  -- ### The KKT conditions for `g ⊗ g`
  have hae2 : ∀ᵐ z ∂gμ, (rankOneGraphon hfm hf0 hf1).toFun z.1 z.2
      = (rankOneGraphon hgm (fun y => le_trans hη.le (hg0 y))
          (fun y => le_trans (hg1 y) (by linarith))).toFun z.1 z.2 := by
    filter_upwards [ae_gμ_of_ae_unitμ hfg] with z hz
    simp only [rankOneGraphon_toFun, hz.1, hz.2]
  have hkktg : SatisfiesKKT H p r μ (rankOneGraphon hgm (fun y => le_trans hη.le (hg0 y))
      (fun y => le_trans (hg1 y) (by linarith))) :=
    ⟨hkkt.1, by rw [← tDensity_congr_ae H hae2]; exact hkkt.2.1,
      isStationary_congr_ae H hae2 hkkt.2.2⟩
  obtain ⟨a, b, hab⟩ := stationary_rank_one_two_values H hd hreg hp0 hp1 hη hgm hg0 hg1 hkktg
  -- ### Two distinct values, each on a set of positive measure
  have hncg : ¬ ∃ c : ℝ, ∀ᵐ y ∂unitμ, g y = c := by
    rintro ⟨c, hc⟩
    exact hnc ⟨c, by filter_upwards [hfg, hc] with y h1 h2; rw [h1, h2]⟩
  have hpos : ∀ u v : ℝ, (∀ᵐ y ∂unitμ, g y = u ∨ g y = v) → unitμ {y | g y = u} ≠ 0 := by
    intro u v huv h0
    refine hncg ⟨v, ?_⟩
    filter_upwards [huv, measure_eq_zero_iff_ae_notMem.mp h0] with y hy hy'
    exact hy.resolve_left hy'
  have hab' : ∀ᵐ y ∂unitμ, g y = b ∨ g y = a := hab.mono fun y hy => hy.symm
  have hne : a ≠ b := by
    rintro rfl
    exact hncg ⟨a, hab.mono fun y hy => hy.elim id id⟩
  obtain ⟨s, t, hst, hst_ae, hposs, hpost⟩ : ∃ s t : ℝ, s < t ∧
      (∀ᵐ y ∂unitμ, g y = s ∨ g y = t) ∧ unitμ {y | g y = s} ≠ 0 ∧
        unitμ {y | g y = t} ≠ 0 := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, h, hab, hpos a b hab, hpos b a hab'⟩
    · exact ⟨b, a, h, hab', hpos b a hab', hpos a b hab⟩
  obtain ⟨xs, hxs⟩ := nonempty_of_measure_ne_zero hposs
  obtain ⟨xt, hxt⟩ := nonempty_of_measure_ne_zero hpost
  have hs0 : 0 < s := lt_of_lt_of_le hη (le_of_le_of_eq (hg0 xs) hxs)
  have ht1 : t < 1 := lt_of_le_of_lt (le_of_eq_of_le hxt.symm (hg1 xt)) (by linarith)
  -- ### The block `A = [0,1] ∩ {g = s}` and its measure `α ∈ (0,1)`
  set A : Set ℝ := Set.Icc (0:ℝ) 1 ∩ {y | g y = s} with hAdef
  have hLs : MeasurableSet {y | g y = s} := measurableSet_eq_fun hgm measurable_const
  have hLt : MeasurableSet {y | g y = t} := measurableSet_eq_fun hgm measurable_const
  have hA : MeasurableSet A := measurableSet_Icc.inter hLs
  have hAsub : A ⊆ Set.Icc 0 1 := Set.inter_subset_left
  have hvolA : volume A = unitμ {y | g y = s} := by
    rw [unitμ, Measure.restrict_apply hLs, hAdef, Set.inter_comm]
  have hdisj : Disjoint {y | g y = s} {y | g y = t} :=
    Set.disjoint_left.mpr fun y h1 h2 => ne_of_lt hst (h1.symm.trans h2)
  have hsum : unitμ {y | g y = s} + unitμ {y | g y = t} ≤ 1 := by
    rw [← measure_union hdisj hLt, ← measure_univ (μ := unitμ)]
    exact measure_mono (Set.subset_univ _)
  have hfinA : unitμ {y | g y = s} ≠ ⊤ := measure_ne_top _ _
  have hfinT : unitμ {y | g y = t} ≠ ⊤ := measure_ne_top _ _
  set α : ℝ := (volume A).toReal with hαdef
  have hα0 : 0 < α := by
    rw [hαdef, hvolA]; exact ENNReal.toReal_pos hposs hfinA
  have hα1 : α < 1 := by
    have htpos : 0 < (unitμ {y | g y = t}).toReal := ENNReal.toReal_pos hpost hfinT
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hsum
    rw [ENNReal.toReal_add hfinA hfinT, ENNReal.toReal_one] at h
    rw [hαdef, hvolA]; linarith
  -- ### Relabelling `A` onto `[0,α]`
  have hIcc : ∀ᵐ x ∂unitμ, x ∈ Set.Icc (0:ℝ) 1 := by
    rw [unitμ, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun x hx => hx
  have hmp := measurePreserving_relabel hA hAsub
  have hrange : ∀ᵐ x ∂unitμ, relabel A x ∈ Set.Icc (0:ℝ) 1 :=
    hmp.quasiMeasurePreserving.ae hIcc
  have hkey : ∀ᵐ x ∂unitμ, f x
      = (Set.Icc 0 α).indicator (fun _ => s) (relabel A x)
        + (Set.Ioc α 1).indicator (fun _ => t) (relabel A x) := by
    filter_upwards [relabel_mem_Icc_iff_mem_ae hA hAsub, hrange, hst_ae, hIcc, hfg]
      with x hm hr hx hx01 hfgx
    rw [hfgx]
    by_cases hxA : x ∈ A
    · have h1 : relabel A x ∈ Set.Icc 0 α := hm.mpr hxA
      have h2 : relabel A x ∉ Set.Ioc α 1 := fun h => absurd h1.2 (not_le.mpr h.1)
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
      exact hxA.2
    · have h1 : relabel A x ∉ Set.Icc 0 α := fun h => hxA (hm.mp h)
      have h2 : relabel A x ∈ Set.Ioc α 1 :=
        ⟨lt_of_not_ge fun hle => h1 ⟨hr.1, hle⟩, hr.2⟩
      have hgt : g x = t := hx.resolve_left fun hs => hxA ⟨hx01, hs⟩
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]
      exact hgt
  -- ### The inverse relabelling
  obtain ⟨τ, hτ, -, hστ⟩ := (isRelabelling_relabel hA hAsub).exists_symm
  refine ⟨α, s, t, ⟨hα0, hα1⟩, hs0, hst, ht1, τ, hτ, ?_⟩
  have hpull := hτ.measurePreserving.quasiMeasurePreserving.ae hkey
  filter_upwards [hpull, hστ] with y h1 h2
  rw [h1, h2]

end SingularEndpoint

end UpperTailOptimizers
