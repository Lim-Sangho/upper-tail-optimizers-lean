import UpperTailOptimizers.Preliminaries.KRRSAnalyticExtension.PsiExists

/-!
# The Kenyon–Radin–Ren–Sadun statements of Appendix B

Appendix B (`app:krrs-analytic-extension`) of `paper/paper.tex` opens with the sentence

> We first record the results from \[KRR–S\] needed for the proof of
> `thm:krrs-analytic-extension`, restricting throughout to `d`-regular graphs.

These are `thm:krrs-bipodality` (their Theorem 1.1) and `thm:krrs-cross-density` (their
Theorem 3.3).  Neither is assumed in this development.  Theorem 3.3 of Kenyon–Radin–Ren–Sadun,
*Bipodal structure in oversaturated random graphs* (arXiv:1509.05370; IMRN 2018,
`kenyon2014entropy`), is packaged here as the structure `KRRSZeta` and proved as `krrs_thm33`:
the cross density `ζ_d` is constructed and the assertions of `thm:krrs-cross-density` are
proved, with the guard `z ≠ ε` explained below (unique critical point, at which `ψ_d(ε,·)`
attains its maximum; strictly decreasing; involution; unique fixed point `(d-1)/d`), in
`Preliminaries/KRRSAnalyticExtension/PsiSymmetry.lean`, `Preliminaries/KRRSAnalyticExtension/PsiRatio.lean`, `Preliminaries/KRRSAnalyticExtension/PsiIntegral.lean`, `Preliminaries/KRRSAnalyticExtension/PsiCritical.lean`,
`Preliminaries/KRRSAnalyticExtension/PsiUnique.lean`, `Preliminaries/KRRSAnalyticExtension/PsiCompare.lean` and `Preliminaries/KRRSAnalyticExtension/PsiExists.lean`, following the source's
own Steps 1–5.  The source's further claim that `ζ_d'` is nowhere zero is omitted, as in the
paper (`rmk:krrs-omitted-identity`).  Their Theorem 1.1, the bipodality of the fixed-density
entropy maximizer, is proved for `d`-regular `H` in `UpperTailOptimizers/Preliminaries/KRRSBipodality/`
(`KRRSFamily.isOptimal`) and enters the appendix through `Preliminaries/KRRSAnalyticExtension/FamilyCore.lean` and
`Preliminaries/KRRSAnalyticExtension/Main.lean`.

## A note on `ψ_d` at `z = ε`

`psiD d ε ε = 0 / 0 = 0` under Lean's junk-value convention, whereas the paper fills the
removable singularity with the honest limit.  Every clause below that quantifies over `z`
therefore carries the guard `z ≠ ε`.  Without it `isMax` would be *false*: `ψ_d(ε,·)` is
strictly negative off the diagonal (`psiD_neg`), so the junk value `0` at `z = ε` beats every
honest one.  `psiFill` (`Preliminaries/KRRSAnalyticExtension/PsiFill.lean`) fills the singularity with the limit, and
`krrs_cross_density` states `thm:krrs-cross-density` for it, without the guard.
-/

namespace UpperTailOptimizers

open MeasureTheory Real Filter Topology

/-! ### KRR–S `thm:krrs-cross-density`: the cross-density selector `ζ_d` -/

/-- **Kenyon–Radin–Ren–Sadun, Theorem 3.3**, recorded in the paper as
`thm:krrs-cross-density`. In the notation used here:

> For fixed `k` and `ε`, there is a unique solution to `∂ψ_k(ε,ε̃)/∂ε̃ = 0`, which we
> denote `ε̃ = ζ_k(ε)`.  The function `ζ_k` is strictly decreasing, with nowhere-vanishing
> derivative and with fixed point at `ε = (k-1)/k`.  Furthermore, `ζ_k` is an involution.

together with the variational characterisation of `ζ_d` as the *maximizer* of
`z ↦ ψ_d(ε,z)`, which is how their §4 produces it and how `paper/paper.tex` introduces
it in `sec:preliminaries`.  The paper's `thm:krrs-cross-density` restates the theorem for
`d ≥ 2` with that characterisation built in (the unique critical point is where `ψ_d(ε,·)`
attains its maximum on `(0,1)`) and without the nowhere-vanishing-derivative clause
(`rmk:krrs-omitted-identity`).

The fields are `mem_Ioo`, `isMax` and `strictAntiOn`; the involution and the fixed point are
`zetaFun_involutive` and `zetaFun_rStar`.  The "nowhere-vanishing derivative" clause is not
transcribed, because the development never differentiates `ζ_d`.

This is a bundle of *proved* facts, not of assumptions: `krrs_thm33` below constructs one,
with `zetaFun` of `Preliminaries/KRRSAnalyticExtension/PsiExists.lean` as the selector.  It is kept as a structure so that the
rest of the appendix reads as it does in the paper, quantified over "the" cross density. -/
structure KRRSZeta (d : ℕ) where
  /-- The KRR–S cross density `ζ_d`. -/
  zeta : ℝ → ℝ
  /-- `ζ_d` maps interior densities to interior densities. -/
  mem_Ioo : ∀ ε ∈ Set.Ioo (0:ℝ) 1, zeta ε ∈ Set.Ioo (0:ℝ) 1
  /-- `ζ_d(ε)` maximises `z ↦ ψ_d(ε,z)` over `(0,1)`.  The guard `z ≠ ε` is Lean's, not
  the paper's: see the module docstring. -/
  isMax : ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ z ∈ Set.Ioo (0:ℝ) 1, z ≠ ε →
    psiD d ε z ≤ psiD d ε (zeta ε)
  /-- `ζ_d` is strictly decreasing.

  Uniqueness of the critical point, the fixed point at `(d-1)/d` and the involution property —
  the remaining clauses of Theorem 3.3 — are not listed as fields: they are *derived* from
  these four below, from Steps 1–4 of the source's own proof (`Preliminaries/KRRSAnalyticExtension/PsiSymmetry.lean`,
  `Preliminaries/KRRSAnalyticExtension/PsiCritical.lean`, `Preliminaries/KRRSAnalyticExtension/PsiUnique.lean`). -/
  strictAntiOn : StrictAntiOn zeta (Set.Ioo (0:ℝ) 1)

/-- **Kenyon–Radin–Ren–Sadun, Theorem 3.3 and the maximizer characterisation in §4**
(arXiv:1509.05370); see `thm:krrs-cross-density`, whose statement includes the maximizer
characterisation, and `rmk:krrs-omitted-identity`.

This is a **theorem**, not an axiom: the cross density is `zetaFun`, the off-diagonal critical
point of `ψ_d(ε,·)`, which exists (`exists_crit`) and is unique (`crit_unique`); it maximises
`ψ_d(ε,·)` (`zetaFun_isMax`) and is strictly decreasing (`zetaFun_strictAntiOn`).  The proof
follows the source's Steps 1–5, with Step 4 replaced — see `Preliminaries/KRRSAnalyticExtension/PsiCritical.lean`. -/
theorem krrs_thm33 (d : ℕ) (hd : 2 ≤ d) : Nonempty (KRRSZeta d) :=
  ⟨{ zeta := zetaFun d
     mem_Ioo := fun _ hε => zetaFun_mem hd hε
     isMax := fun _ hε z hz hne => zetaFun_isMax hd hε z hz hne
     strictAntiOn := zetaFun_strictAntiOn hd }⟩

/-! ### Consequences of the `thm:krrs-cross-density` input

The paper's "Since `Ū` avoids `ε_*`, the fixed-point assertion in `thm:krrs-cross-density`
gives `ζ_d(ε) ≠ ε`" (paragraph 4 of the proof of `thm:krrs-analytic-extension`) and the step
closing paragraph 1, where `z₀ = ε_*` "implies `ε₀ = (d-1)/d`", are *derived* here, not
assumed: a strictly decreasing map is injective, so it has at most one fixed point, and
`(d-1)/d` is one. -/

theorem rStar_mem_Ioo {d : ℕ} (hd : 2 ≤ d) : rStar d ∈ Set.Ioo (0:ℝ) 1 := by
  have hd0 : (0:ℝ) < (d : ℝ) := by
    have : (0:ℕ) < d := by omega
    exact_mod_cast this
  have hd1 : (1:ℝ) ≤ (d : ℝ) - 1 := by
    have : (2:ℕ) ≤ d := hd
    have : (2:ℝ) ≤ (d : ℝ) := by exact_mod_cast this
    linarith
  constructor
  · unfold rStar
    positivity
  · unfold rStar
    rw [div_lt_one hd0]
    linarith

/-- **`ζ_d` fixes the exceptional density** — Step 1 of Kenyon–Radin–Ren–Sadun, Theorem 3.3,
here a theorem rather than an assumption.

At `ε = r_*` the function `ψ_d(r_*,·)` has *no* off-diagonal critical point (`no_crit_rStar`),
whereas an off-diagonal maximizer would be one (`Wr_eq_zero_of_isMax`).  So the maximizer is
the diagonal point itself. -/
theorem KRRSZeta.fixed {d : ℕ} (hd : 2 ≤ d) (Z : KRRSZeta d) : Z.zeta (rStar d) = rStar d := by
  by_contra hne
  have hr0 : 0 < rStar d := rStar_pos hd
  have hr1 : rStar d < 1 := rStar_lt_one hd
  have hrmem : rStar d ∈ Set.Ioo (0:ℝ) 1 := ⟨hr0, hr1⟩
  have hz := Z.mem_Ioo (rStar d) hrmem
  have hcrit : Wr d (rStar d) (Z.zeta (rStar d)) = 0 :=
    Wr_eq_zero_of_isMax hd hr0 hz.1 hz.2 hne hne
      (fun w hw0 hw1 hwne => Z.isMax (rStar d) hrmem w ⟨hw0, hw1⟩ hwne)
  exact no_crit_rStar hd hz.1 hz.2 hne hcrit

/-- `ζ_d(ε) ≠ ε` away from the exceptional density: a strictly decreasing function has at
most one fixed point, and `ζ_d` already fixes `(d-1)/d`. -/
theorem KRRSZeta.ne_self {d : ℕ} (hd : 2 ≤ d) (Z : KRRSZeta d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0:ℝ) 1) (hne : ε ≠ rStar d) : Z.zeta ε ≠ ε := by
  intro hfix
  rcases lt_trichotomy ε (rStar d) with hlt | heq | hgt
  · have := Z.strictAntiOn hε (rStar_mem_Ioo hd) hlt
    rw [hfix, Z.fixed hd] at this
    exact absurd this (not_lt.mpr hlt.le)
  · exact hne heq
  · have := Z.strictAntiOn (rStar_mem_Ioo hd) hε hgt
    rw [hfix, Z.fixed hd] at this
    exact absurd this (not_lt.mpr hgt.le)

/-- `ζ_d(ε) ≠ (d-1)/d` away from the exceptional density: `ζ_d` is injective, being strictly
decreasing, and already sends `(d-1)/d` there. -/
theorem KRRSZeta.ne_rStar {d : ℕ} (hd : 2 ≤ d) (Z : KRRSZeta d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0:ℝ) 1) (hne : ε ≠ rStar d) : Z.zeta ε ≠ rStar d := by
  intro hz
  exact hne (Z.strictAntiOn.injOn hε (rStar_mem_Ioo hd) (by rw [hz, Z.fixed hd]))

/-- **Uniqueness of the critical point** — the clause Theorem 3.3 opens with, here a theorem.
`ζ_d(ε)` is a critical point because it is an interior off-diagonal maximizer, and `crit_unique`
(Step 4) says there is at most one. -/
theorem KRRSZeta.uniqueCritical {d : ℕ} (hd : 2 ≤ d) (Z : KRRSZeta d) :
    ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ z ∈ Set.Ioo (0:ℝ) 1, z ≠ ε → Wr d ε z = 0 → z = Z.zeta ε := by
  intro ε hε z hz hzne hcrit
  have hεr : ε ≠ rStar d := by
    intro h
    rw [h] at hcrit hzne
    exact no_crit_rStar hd hz.1 hz.2 hzne hcrit
  have hzne' : Z.zeta ε ≠ ε := Z.ne_self hd hε hεr
  have hzstar : Z.zeta ε ≠ rStar d := Z.ne_rStar hd hε hεr
  have hzm := Z.mem_Ioo ε hε
  have hcrit' : Wr d ε (Z.zeta ε) = 0 :=
    Wr_eq_zero_of_isMax hd hε.1 hzm.1 hzm.2 hzne' hzstar
      (fun w hw0 hw1 hwne => Z.isMax ε hε w ⟨hw0, hw1⟩ hwne)
  exact crit_unique hd hε.1 hε.2 hz.1 hz.2 hzm.1 hzm.2 hzne hzne' hcrit hcrit'

/-- **`ζ_d` is an involution** — Step 3 of Kenyon–Radin–Ren–Sadun, Theorem 3.3, here a
theorem rather than an assumption.

Away from the exceptional density the argument is theirs: `ζ_d(ε)` maximises `ψ_d(ε,·)`, so
it is a critical point (`Wr_eq_zero_of_isMax`); the critical-point equation is symmetric
(`Wr_swap`), so `ε` is a critical point of `ψ_d(ζ_d(ε),·)`; and `uniqueCritical` identifies
it as `ζ_d(ζ_d(ε))`.  At the exceptional density itself it is `fixed` applied twice. -/
theorem KRRSZeta.involutive {d : ℕ} (hd : 2 ≤ d) (Z : KRRSZeta d) :
    ∀ ε ∈ Set.Ioo (0:ℝ) 1, Z.zeta (Z.zeta ε) = ε := by
  intro ε hε
  by_cases hne : ε = rStar d
  · rw [hne, Z.fixed hd, Z.fixed hd]
  · have hz := Z.mem_Ioo ε hε
    have hzne : Z.zeta ε ≠ ε := Z.ne_self hd hε hne
    have hzstar : Z.zeta ε ≠ rStar d := Z.ne_rStar hd hε hne
    have hcrit : Wr d ε (Z.zeta ε) = 0 :=
      Wr_eq_zero_of_isMax hd hε.1 hz.1 hz.2 hzne hzstar
        (fun w hw0 hw1 hwne => Z.isMax ε hε w ⟨hw0, hw1⟩ hwne)
    exact (Z.uniqueCritical hd (Z.zeta ε) hz ε hε (Ne.symm hzne) (Wr_eq_zero_swap hcrit)).symm

end UpperTailOptimizers
