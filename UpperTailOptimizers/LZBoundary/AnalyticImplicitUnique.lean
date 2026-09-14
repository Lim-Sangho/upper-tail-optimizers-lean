import UpperTailOptimizers.LZBoundary.AnalyticIFT

/-!
# Local uniqueness in the real-analytic implicit function theorem

`UpperTailOptimizers.analytic_implicit` (`LZBoundary/AnalyticIFT.lean`) produces an analytic
solution family `z(p)` of `F (z p) p = 0` through `z₀`, but its statement says nothing
about that family being the *only* solution nearby.  The uniqueness is nevertheless already
present in its proof: the Φ-trick runs through `analytic_inverse`, and the `Set.InjOn`
clause of `analytic_inverse` is exactly local uniqueness for the augmented map
`Φ (z, p) = (F z p, p)`.  This file re-runs that proof and exposes the clause.

The upgraded statement `analytic_implicit_unique` names the two neighbourhoods: an open
`S ∋ z₀` and an open `T ∋ p₀` such that for every parameter `p ∈ T`, the value `z p` is the
*unique* zero of `F · p` inside `S`.  The shrinking from the source neighbourhood of
`analytic_inverse` (a set in `E × P`, not a box) to a genuine product `S ×ˢ T` uses
`isOpen_prod_iff`; `T` is then cut down further, to the interior of the set of parameters
for which the inverse map lands in `S` and inverts `Φ`.

The consumer is `lem:rank-one-kkt-family` of `paper/sections/singular.tex`.  The
desingularized family system of `SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean` is invariant under `h ↦ -h`,
so `h ↦ z (-h)` solves it as well; local uniqueness in the above sense is what forces the
symmetries `u_{-h} = u_h`, `p_{-h} = p_h`, `γ_{-h} = γ_h` stated by that lemma.  (The Lean
family is solved jointly for `(u_h, ℓ_h, γ_h)` with `ℓ_h = ℓ(p_h)`, so uniqueness gives all
three at once; the paper applies it only to `u_h` and reads off the evenness of `γ_h` and
`p_h` from their explicit formulas.)  The
germ form `analytic_implicit_locally_unique` is the shape that argument applies directly.

## Contents

* `analytic_implicit_unique` — the analytic implicit function theorem with explicit
  neighbourhoods `S ∋ z₀`, `T ∋ p₀` and uniqueness of the zero of `F · p` in `S`;
* `analytic_implicit_locally_unique` — the germ form: every continuous solution family
  through `z₀` agrees with `z` on a neighbourhood of `p₀`.
-/

open Filter Topology

namespace UpperTailOptimizers

/-- **Real-analytic implicit function theorem, with local uniqueness.**

Same hypotheses as `analytic_implicit`: `F : E → P → E` is jointly analytic at `(z₀, p₀)`,
vanishes there, and its partial `z`-derivative at the base point is the continuous linear
equivalence `L`.  The conclusion adds explicit neighbourhoods `S ∋ z₀` and `T ∋ p₀` and the
uniqueness clause: for `p ∈ T`, the point `z p` is the *only* `w ∈ S` with `F w p = 0`.

The proof is the Φ-trick of `analytic_implicit` — `Φ (z, p) = (F z p, p)` has block
upper-triangular invertible strict derivative, so `analytic_inverse` applies to it — but it
keeps the `Set.InjOn Φ` clause that `analytic_implicit` discards.

Used by `lem:rank-one-kkt-family` to force the `h ↦ -h` symmetries of the
coalescing scalar family. -/
theorem analytic_implicit_unique {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {F : E → P → E} {z₀ : E} {p₀ : P}
    (hF : AnalyticAt ℝ (fun w : E × P => F w.1 w.2) (z₀, p₀))
    (hF0 : F z₀ p₀ = 0)
    (L : E ≃L[ℝ] E)
    (hL : HasStrictFDerivAt (fun z : E => F z p₀) (L : E →L[ℝ] E) z₀) :
    ∃ (S : Set E) (T : Set P) (z : P → E),
      IsOpen S ∧ z₀ ∈ S ∧ IsOpen T ∧ p₀ ∈ T ∧
      z p₀ = z₀ ∧ AnalyticAt ℝ z p₀ ∧
      (∀ p ∈ T, z p ∈ S) ∧
      (∀ p ∈ T, F (z p) p = 0) ∧
      (∀ p ∈ T, ∀ w ∈ S, F w p = 0 → w = z p) := by
  classical
  -- The augmented map and its strict derivative, exactly as in `analytic_implicit`.
  set Φ : E × P → E × P := fun w => (F w.1 w.2, w.2) with hΦdef
  set Fjoint : E × P → E := fun w => F w.1 w.2 with hFjdef
  set G : (E × P) →L[ℝ] E := fderiv ℝ Fjoint (z₀, p₀) with hGdef
  have hGstrict : HasStrictFDerivAt Fjoint G (z₀, p₀) := hF.hasStrictFDerivAt
  set inlCLM : E →L[ℝ] (E × P) :=
    (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] P) with hinldef
  have hincl : HasStrictFDerivAt (fun z : E => (z, p₀)) inlCLM z₀ :=
    (hasStrictFDerivAt_id z₀).prodMk (hasStrictFDerivAt_const p₀ z₀)
  have hrestr : HasStrictFDerivAt (fun z : E => F z p₀) (G.comp inlCLM) z₀ := by
    have := hGstrict.comp z₀ hincl
    simpa [hFjdef] using this
  have hGL : G.comp inlCLM = (L : E →L[ℝ] E) :=
    hrestr.hasFDerivAt.unique hL.hasFDerivAt
  set inrCLM : P →L[ℝ] (E × P) :=
    (0 : P →L[ℝ] E).prod (ContinuousLinearMap.id ℝ P) with hinrdef
  set B : P →L[ℝ] E := G.comp inrCLM with hBdef
  have hGdecomp : ∀ w : E × P, G w = L w.1 + B w.2 := by
    intro w
    have hsplit : w = inlCLM w.1 + inrCLM w.2 := by
      simp [hinldef, hinrdef]
    calc
      G w = G (inlCLM w.1 + inrCLM w.2) := by rw [← hsplit]
      _ = G (inlCLM w.1) + G (inrCLM w.2) := by rw [map_add]
      _ = (G.comp inlCLM) w.1 + (G.comp inrCLM) w.2 := by
            simp [ContinuousLinearMap.comp_apply]
      _ = L w.1 + B w.2 := by simp only [hGL, hBdef, ContinuousLinearEquiv.coe_coe]
  set DΦ : ((E × P)) →L[ℝ] (E × P) :=
    G.prod (ContinuousLinearMap.snd ℝ E P) with hDΦdef
  have hΦstrict : HasStrictFDerivAt Φ DΦ (z₀, p₀) := by
    have h2 : HasStrictFDerivAt (fun w : E × P => w.2)
        (ContinuousLinearMap.snd ℝ E P) (z₀, p₀) := hasStrictFDerivAt_snd
    have := hGstrict.prodMk h2
    simpa [hΦdef, hFjdef, hDΦdef] using this
  set Ψ : (E × P) →L[ℝ] (E × P) :=
    ((L.symm : E →L[ℝ] E).comp
        ((ContinuousLinearMap.fst ℝ E P)
          - B.comp (ContinuousLinearMap.snd ℝ E P))).prod
      (ContinuousLinearMap.snd ℝ E P) with hΨdef
  have hΨapply : ∀ w : E × P, Ψ w = (L.symm (w.1 - B w.2), w.2) := by
    intro w
    simp [hΨdef, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
  have hDΦapply : ∀ w : E × P, DΦ w = (G w, w.2) := by
    intro w
    simp [hDΦdef, ContinuousLinearMap.prod_apply]
  have hleft : Function.LeftInverse Ψ DΦ := by
    intro w
    rw [hDΦapply w, hΨapply]
    simp only
    have : G w - B w.2 = L w.1 := by rw [hGdecomp w]; abel
    rw [this]
    simp
  have hright : Function.RightInverse Ψ DΦ := by
    intro w
    rw [hΨapply w, hDΦapply]
    simp only
    have hG' : G (L.symm (w.1 - B w.2), w.2) = w.1 := by
      rw [hGdecomp]
      simp
    rw [hG']
  set DΦcle : (E × P) ≃L[ℝ] (E × P) :=
    ContinuousLinearEquiv.equivOfInverse DΦ Ψ hleft hright with hDΦcledef
  have hcle_coe : (DΦcle : (E × P) →L[ℝ] (E × P)) = DΦ := rfl
  have hΦstrict' : HasStrictFDerivAt Φ (DΦcle : (E × P) →L[ℝ] (E × P)) (z₀, p₀) := by
    rw [hcle_coe]; exact hΦstrict
  have hΦ0 : Φ (z₀, p₀) = (0, p₀) := by simp [hΦdef, hF0]
  have hΦanalytic : AnalyticAt ℝ Φ (z₀, p₀) := by
    have hsnd : AnalyticAt ℝ (fun w : E × P => w.2) (z₀, p₀) := analyticAt_snd
    have := hF.prod hsnd
    simpa [hΦdef, hFjdef] using this
  -- The analytic inverse function theorem, *with* its injectivity clause.
  obtain ⟨S', T', Γ, hS'open, hmemS', hT'open, hmemT', _hmapsΦ, _hmapsΓ, hΓΦ, hΦΓ, hinj,
    hΓan⟩ := analytic_inverse hΦanalytic DΦcle hΦstrict'
  rw [hΦ0] at hmemT' hΓan
  -- The implicit family.
  set z : P → E := fun p => (Γ ((0 : E), p)).1 with hzdef
  have hz0 : z p₀ = z₀ := by
    have h := hΓΦ (z₀, p₀) hmemS'
    rw [hΦ0] at h
    show (Γ ((0 : E), p₀)).1 = z₀
    rw [h]
  have hzan : AnalyticAt ℝ z p₀ := by
    have hmap : AnalyticAt ℝ (fun p : P => ((0 : E), p)) p₀ :=
      AnalyticAt.prod analyticAt_const analyticAt_id
    exact analyticAt_fst.comp (hΓan.comp hmap)
  -- Shrink the source neighbourhood `S'` to a product box `S ×ˢ T₀`.
  obtain ⟨S, T₀, hSopen, hT₀open, hz₀S, hp₀T₀, hbox⟩ :=
    isOpen_prod_iff.mp hS'open z₀ p₀ hmemS'
  -- Cut the parameter set down to those `p` for which the family behaves.
  set A : Set P := {p : P | p ∈ T₀ ∧ ((0 : E), p) ∈ T' ∧ z p ∈ S} with hAdef
  have hA : A ∈ 𝓝 p₀ := by
    have h1 : ∀ᶠ p in 𝓝 p₀, p ∈ T₀ := hT₀open.eventually_mem hp₀T₀
    have h2 : ∀ᶠ p in 𝓝 p₀, ((0 : E), p) ∈ T' := by
      have hc : ContinuousAt (fun p : P => ((0 : E), p)) p₀ := by fun_prop
      exact hc.eventually (hT'open.eventually_mem hmemT')
    have h3 : ∀ᶠ p in 𝓝 p₀, z p ∈ S := by
      have : z p₀ ∈ S := by rw [hz0]; exact hz₀S
      exact hzan.continuousAt.eventually (hSopen.eventually_mem this)
    filter_upwards [h1, h2, h3] with p hp1 hp2 hp3 using ⟨hp1, hp2, hp3⟩
  -- For every `p ∈ A`, the inverse map really does invert `Φ` over `(0, p)`.
  have hkey : ∀ p ∈ A, (Γ ((0 : E), p)).2 = p ∧ F (z p) p = 0 := by
    intro p hp
    have h := hΦΓ ((0 : E), p) hp.2.1
    have hsnd : (Γ ((0 : E), p)).2 = p := by
      have := congrArg Prod.snd h
      simpa [hΦdef] using this
    refine ⟨hsnd, ?_⟩
    have hfst : F (Γ ((0 : E), p)).1 (Γ ((0 : E), p)).2 = 0 := by
      have := congrArg Prod.fst h
      simpa [hΦdef] using this
    rw [hsnd] at hfst
    exact hfst
  refine ⟨S, interior A, z, hSopen, hz₀S, isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hA, hz0, hzan, ?_, ?_, ?_⟩
  · intro p hp
    exact (interior_subset hp).2.2
  · intro p hp
    exact (hkey p (interior_subset hp)).2
  · intro p hp w hwS hw
    have hp' : p ∈ A := interior_subset hp
    have hmem1 : (w, p) ∈ S' := hbox (Set.mk_mem_prod hwS hp'.1)
    have hmem2 : (z p, p) ∈ S' := hbox (Set.mk_mem_prod hp'.2.2 hp'.1)
    have hΦw : Φ (w, p) = ((0 : E), p) := by simp [hΦdef, hw]
    have hΦz : Φ (z p, p) = ((0 : E), p) := by simp [hΦdef, (hkey p hp').2]
    have := hinj hmem1 hmem2 (hΦw.trans hΦz.symm)
    exact congrArg Prod.fst this

/-- **Real-analytic implicit function theorem, germ form of local uniqueness.**

The family `z` of `analytic_implicit` is the only continuous solution family through `z₀`:
any `z'` continuous at `p₀` with `z' p₀ = z₀` and `F (z' p) p = 0` near `p₀` agrees with `z`
near `p₀`.

This is the form used for `lem:rank-one-kkt-family`: applied to `z' p := z (-p)`
— legitimate because the desingularized system of `SingularEndpoint/RankOneStationaryFamily/FamilySystem.lean` is invariant
under `h ↦ -h` — it yields the symmetries of the coalescing scalar family. -/
theorem analytic_implicit_locally_unique {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {F : E → P → E} {z₀ : E} {p₀ : P}
    (hF : AnalyticAt ℝ (fun w : E × P => F w.1 w.2) (z₀, p₀))
    (hF0 : F z₀ p₀ = 0)
    (L : E ≃L[ℝ] E)
    (hL : HasStrictFDerivAt (fun z : E => F z p₀) (L : E →L[ℝ] E) z₀) :
    ∃ z : P → E,
      z p₀ = z₀ ∧
      (∀ᶠ p in 𝓝 p₀, F (z p) p = 0) ∧
      AnalyticAt ℝ z p₀ ∧
      (∀ z' : P → E, ContinuousAt z' p₀ → z' p₀ = z₀ →
        (∀ᶠ p in 𝓝 p₀, F (z' p) p = 0) → ∀ᶠ p in 𝓝 p₀, z' p = z p) := by
  obtain ⟨S, T, z, hSopen, hz₀S, hTopen, hp₀T, hz0, hzan, _hzS, hzsol, huniq⟩ :=
    analytic_implicit_unique hF hF0 L hL
  have hTev : ∀ᶠ p in 𝓝 p₀, p ∈ T := hTopen.eventually_mem hp₀T
  refine ⟨z, hz0, ?_, hzan, ?_⟩
  · filter_upwards [hTev] with p hp using hzsol p hp
  · intro z' hz'cont hz'0 hz'sol
    have hz'S : ∀ᶠ p in 𝓝 p₀, z' p ∈ S := by
      have : z' p₀ ∈ S := by rw [hz'0]; exact hz₀S
      exact hz'cont.eventually (hSopen.eventually_mem this)
    filter_upwards [hTev, hz'S, hz'sol] with p hp hpS hpsol
    exact huniq p hp (z' p) hpS hpsol

end UpperTailOptimizers
