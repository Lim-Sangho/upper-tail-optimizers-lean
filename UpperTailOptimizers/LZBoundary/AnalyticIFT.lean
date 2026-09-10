import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions

/-!
# A real-analytic implicit function theorem

`analytic_implicit`: given `F : E → P → E` (unknown in a complete real normed space `E`,
parameter in a complete real normed space `P`) jointly analytic at `(z₀, p₀)` with
`F z₀ p₀ = 0` and invertible partial `z`-derivative `L`, there is an analytic map `z(p)`
through `z₀` solving `F (z p) p = 0` near `p₀`.

Proof via the Φ-trick: `Φ(z,p) = (F z p, p)` is a local analytic diffeomorphism (its
derivative is block upper-triangular with invertible blocks `L`, `id`), so `Φ.symm` is
analytic (`OpenPartialHomeomorph.analyticAt_symm'`) and the implicit map is the first
component of `Φ.symm (0, p)`.

This is the analytic implicit function theorem absent from Mathlib v4.28.0.  Two
specialisations are used in the development:

* `analytic_implicit_two_z` / `analytic_implicit_two` — two equations, two unknowns, one
  scalar parameter: the analyticity of the Lubetzky–Zhao contact maps (`thm:scalar-lz-boundary` of
  `paper/bipodal_optimizer.tex`);
* `analytic_implicit_scalar` — one scalar equation, one scalar unknown, parameters in `P`:
  the analytic critical point `δ_*(p,r)` of Section 6 of `paper/bipodal_optimizer.tex`.

The companion `analytic_inverse` is the **analytic inverse function theorem**
(Krantz–Parks, *A Primer of Real Analytic Functions*, Theorem 2.5.1), used in Appendix A
of `paper/bipodal_optimizer.tex` (`KRRS/Main.lean`).  It is not a corollary of
`analytic_implicit`: besides the analytic local inverse it supplies the *injectivity* of
`F` on the source neighbourhood, which is the entire content of the appendix's uniqueness
clause ("`θ = Γ(y)` is the unique parameter vector in `𝒰` solving (A.1)").
-/

open Filter Topology

namespace UpperTailOptimizers

/-- **Real-analytic inverse function theorem** (Krantz–Parks, Theorem 2.5.1).

If `F : E → E` is analytic at `z₀` with invertible strict derivative `L`, then there are
open neighbourhoods `S ∋ z₀` and `T ∋ F z₀`, and an analytic map `Γ : E → E`, such that `F`
maps `S` into `T`, `Γ` maps `T` into `S`, the two are mutually inverse there, and — the
clause that `analytic_implicit` does *not* give — `F` is **injective** on `S`.

Everything is read off the local homeomorphism `HasStrictFDerivAt.toOpenPartialHomeomorph`
attached to `F` at `z₀`; analyticity of its inverse is
`OpenPartialHomeomorph.analyticAt_symm'`. -/
theorem analytic_inverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {z₀ : E} (hF : AnalyticAt ℝ F z₀) (L : E ≃L[ℝ] E)
    (hL : HasStrictFDerivAt F (L : E →L[ℝ] E) z₀) :
    ∃ (S T : Set E) (Γ : E → E),
      IsOpen S ∧ z₀ ∈ S ∧ IsOpen T ∧ F z₀ ∈ T ∧
      Set.MapsTo F S T ∧ Set.MapsTo Γ T S ∧
      (∀ z ∈ S, Γ (F z) = z) ∧ (∀ y ∈ T, F (Γ y) = y) ∧
      Set.InjOn F S ∧ AnalyticAt ℝ Γ (F z₀) := by
  classical
  set R : OpenPartialHomeomorph E E := hL.toOpenPartialHomeomorph F with hRdef
  have hRcoe : (R : E → E) = F := rfl
  have hsrc : z₀ ∈ R.source := hL.mem_toOpenPartialHomeomorph_source
  have htgt : F z₀ ∈ R.target := hL.image_mem_toOpenPartialHomeomorph_target
  have hfderiv : fderiv ℝ (R : E → E) z₀ = (L : E →L[ℝ] E) := by
    rw [hRcoe]; exact hL.hasFDerivAt.fderiv
  have hsymm : AnalyticAt ℝ R.symm (R z₀) :=
    R.analyticAt_symm' (i := L) hsrc (by rw [hRcoe]; exact hF) hfderiv
  refine ⟨R.source, R.target, R.symm, R.open_source, hsrc, R.open_target, htgt,
    ?_, ?_, ?_, ?_, R.injOn, ?_⟩
  · intro z hz; exact R.map_source hz
  · intro y hy; exact R.map_target hy
  · intro z hz; exact R.left_inv hz
  · intro y hy; exact R.right_inv hy
  · rw [hRcoe] at hsymm; exact hsymm

/-- **Real-analytic implicit function theorem.**

Given `F : E → P → E` jointly analytic at `(z₀, p₀)`, a base solution `F z₀ p₀ = 0`, and an
invertible partial `z`-derivative `L` (a continuous linear equiv with
`HasStrictFDerivAt (fun z => F z p₀) L z₀`), there is an analytic map `z : P → E` through
`z₀` solving `F (z p) p = 0` near `p₀`. -/
theorem analytic_implicit {E P : Type*}
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
      AnalyticAt ℝ z p₀ := by
  classical
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
  set R : OpenPartialHomeomorph (E × P) (E × P) :=
    hΦstrict'.toOpenPartialHomeomorph Φ with hRdef
  have hRcoe : (R : (E × P) → (E × P)) = Φ := rfl
  have hsrc : (z₀, p₀) ∈ R.source := hΦstrict'.mem_toOpenPartialHomeomorph_source
  have hΦ0 : Φ (z₀, p₀) = (0, p₀) := by simp [hΦdef, hF0]
  have hΦanalytic : AnalyticAt ℝ Φ (z₀, p₀) := by
    have hsnd : AnalyticAt ℝ (fun w : E × P => w.2) (z₀, p₀) := analyticAt_snd
    have := hF.prod hsnd
    simpa [hΦdef, hFjdef] using this
  have hfderivΦ : fderiv ℝ Φ (z₀, p₀) = (DΦcle : (E × P) →L[ℝ] (E × P)) :=
    hΦstrict'.hasFDerivAt.fderiv
  have hsymm_analytic : AnalyticAt ℝ R.symm (R (z₀, p₀)) := by
    apply R.analyticAt_symm' hsrc
    · rw [hRcoe]; exact hΦanalytic
    · rw [hRcoe]; exact hfderivΦ
  rw [hRcoe, hΦ0] at hsymm_analytic
  refine ⟨fun p => (R.symm ((0 : E), p)).1, ?_, ?_, ?_⟩
  · have hinv : R.symm (Φ (z₀, p₀)) = (z₀, p₀) := by
      rw [← hRcoe]; exact R.left_inv hsrc
    rw [hΦ0] at hinv
    show (R.symm ((0 : E), p₀)).1 = z₀
    rw [hinv]
  · have hev : ∀ᶠ y in 𝓝 (R (z₀, p₀)), R (R.symm y) = y :=
      R.eventually_right_inverse' hsrc
    rw [hRcoe, hΦ0] at hev
    have hcont : ContinuousAt (fun p : P => ((0 : E), p)) p₀ := by fun_prop
    have hpull : ∀ᶠ p in 𝓝 p₀, Φ (R.symm ((0 : E), p)) = ((0 : E), p) := by
      have := hcont.eventually hev
      simpa using this
    filter_upwards [hpull] with p hp
    have hp1 : (Φ (R.symm ((0 : E), p))).1 = (0 : E) := by rw [hp]
    have hp2 : (R.symm ((0 : E), p)).2 = p := by
      have := congrArg Prod.snd hp
      simpa [hΦdef] using this
    have : F (R.symm ((0 : E), p)).1 (R.symm ((0 : E), p)).2 = (0 : E) := by
      have := hp1
      simpa [hΦdef] using this
    rw [hp2] at this
    exact this
  · have hmap : AnalyticAt ℝ (fun p : P => ((0 : E), p)) p₀ := by
      apply AnalyticAt.prod
      · exact analyticAt_const
      · exact analyticAt_id
    have hcomp : AnalyticAt ℝ (fun p : P => R.symm ((0 : E), p)) p₀ :=
      hsymm_analytic.comp hmap
    exact analyticAt_fst.comp hcomp

/-- **Real-analytic implicit function theorem, two equations / two unknowns / one parameter.**

Given `F : (ℝ × ℝ) → ℝ → (ℝ × ℝ)` jointly analytic at `(z₀, p₀)`, a base solution
`F z₀ p₀ = 0`, and an invertible partial `z`-Jacobian `L` (a continuous linear equiv with
`HasStrictFDerivAt (fun z => F z p₀) L z₀`), there is an analytic curve `z : ℝ → ℝ × ℝ` through
`z₀` solving `F (z p) p = 0` near `p₀`. -/
theorem analytic_implicit_two_z
    {F : (ℝ × ℝ) → ℝ → (ℝ × ℝ)}
    {z₀ : ℝ × ℝ} {p₀ : ℝ}
    (hF : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => F w.1 w.2) (z₀, p₀))
    (hF0 : F z₀ p₀ = 0)
    (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hL : HasStrictFDerivAt (fun z : ℝ × ℝ => F z p₀) (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) z₀) :
    ∃ z : ℝ → ℝ × ℝ,
      z p₀ = z₀ ∧
      (∀ᶠ p in 𝓝 p₀, F (z p) p = 0) ∧
      AnalyticAt ℝ z p₀ :=
  analytic_implicit hF hF0 L hL

/-- Scalar form of `analytic_implicit_two_z`: analytic implicit functions `a(p), b(p)`. -/
theorem analytic_implicit_two
    {F : (ℝ × ℝ) → ℝ → (ℝ × ℝ)} {z₀ : ℝ × ℝ} {p₀ : ℝ}
    (hF : AnalyticAt ℝ (fun w : (ℝ × ℝ) × ℝ => F w.1 w.2) (z₀, p₀))
    (hF0 : F z₀ p₀ = 0)
    (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hL : HasStrictFDerivAt (fun z : ℝ × ℝ => F z p₀) (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) z₀) :
    ∃ a b : ℝ → ℝ, a p₀ = z₀.1 ∧ b p₀ = z₀.2 ∧
      (∀ᶠ p in 𝓝 p₀, F (a p, b p) p = 0) ∧ AnalyticAt ℝ a p₀ ∧ AnalyticAt ℝ b p₀ := by
  obtain ⟨z, hz0, hzsol, hza⟩ := analytic_implicit_two_z hF hF0 L hL
  refine ⟨fun p => (z p).1, fun p => (z p).2,
    by show (z p₀).1 = z₀.1; rw [hz0], by show (z p₀).2 = z₀.2; rw [hz0], ?_,
    analyticAt_fst.comp hza, analyticAt_snd.comp hza⟩
  filter_upwards [hzsol] with p hp
  simpa only [Prod.mk.eta] using hp

/-- Multiplication by a nonzero scalar, as a continuous linear automorphism of `ℝ`. -/
noncomputable def mulCLE {c : ℝ} (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c)
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹)
    (fun x => by simp [ContinuousLinearMap.smulRight_apply, mul_assoc,
      mul_inv_cancel₀ hc])
    (fun x => by simp [ContinuousLinearMap.smulRight_apply, mul_assoc,
      inv_mul_cancel₀ hc])

@[simp] theorem mulCLE_coe {c : ℝ} (hc : c ≠ 0) :
    (mulCLE hc : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c := rfl

/-- **Real-analytic implicit function theorem, one scalar equation and one scalar unknown,
with parameters in a complete normed space `P`.**

Given `F : ℝ → P → ℝ` jointly analytic at `(z₀, p₀)`, a base solution `F z₀ p₀ = 0`, and a
nonvanishing strict partial derivative `∂_z F (z₀, p₀) = c ≠ 0`, there is an analytic map
`z : P → ℝ` through `z₀` solving `F (z p) p = 0` near `p₀`. -/
theorem analytic_implicit_scalar {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {F : ℝ → P → ℝ} {z₀ c : ℝ} {p₀ : P}
    (hF : AnalyticAt ℝ (fun w : ℝ × P => F w.1 w.2) (z₀, p₀))
    (hF0 : F z₀ p₀ = 0)
    (hc : c ≠ 0)
    (hL : HasStrictDerivAt (fun z : ℝ => F z p₀) c z₀) :
    ∃ z : P → ℝ, z p₀ = z₀ ∧ (∀ᶠ p in 𝓝 p₀, F (z p) p = 0) ∧ AnalyticAt ℝ z p₀ := by
  refine analytic_implicit hF hF0 (mulCLE hc) ?_
  rw [mulCLE_coe hc]
  exact hL.hasStrictFDerivAt

end UpperTailOptimizers
