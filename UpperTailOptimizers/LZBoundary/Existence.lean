import UpperTailOptimizers.LZBoundary.Arc
import UpperTailOptimizers.LZBoundary.PhiConvex
import UpperTailOptimizers.LZBoundary.PhiDeriv
import UpperTailOptimizers.LZBoundary.PhiAsymptotics
import UpperTailOptimizers.LZBoundary.ConvexMinorant
import UpperTailOptimizers.LZBoundary.ContactMono
import UpperTailOptimizers.LZBoundary.ContactBridge

/-!
# Lubetzky–Zhao contacts and existence of regular Lubetzky–Zhao boundary arcs (Lemmas 3.3–3.4, `thm:scalar-lz-boundary`)

This file proves the results of Section 3 of `paper/bipodal_optimizer.tex` (Section 3):

* `lz_boundary_contacts`        — `lem:contact-points` (existence of the two
                              Lubetzky–Zhao contacts and the common-tangent equations),
* `lz_boundary_endpoint_limits` — `lem:contact-point-limits` (limits of the
                              contacts as `p → p_*`, `p → 0`),
* `scalar_lz_boundary_arcs`     — `thm:scalar-lz-boundary` (existence of an
                              oriented regular Lubetzky–Zhao boundary arc through every
                              non-exceptional `r₀`).

## Axiom status

Lemmas 3.3 and 3.4 are proved (`#print axioms` ⇒ `propext, Classical.choice,
Quot.sound` only) from the `Scalar.ConvexMinorant`, `Scalar.PhiDeriv` and
`Scalar.PhiAsymptotics` infrastructure — itself built from Mathlib primitives, since
the *lower convex envelope* and its structure theory, the full one-variable `φ`
derivative/asymptotic analysis, and the subsequence/cluster machinery are **not present
in Mathlib v4.28.0**.

**`thm:scalar-lz-boundary`** (`scalar_lz_boundary_arcs`) is sorry-free and
axiom-clean (`#print axioms scalar_lz_boundary_arcs ⇒ propext, Classical.choice, Quot.sound`,
i.e. only the standard Lean axioms, no project axiom).  It is built on the keystone
`exists_globalContacts` (the global single-valued real-analytic monotone contact maps
`u_a, u_b`, via a multivariate analytic implicit function theorem absent from Mathlib
v4.28.0), the construction half `arcMaps_of_globalContacts` (the `ordering`,
`supporting` and `secondContact` fields, by inverting the relevant contact family), and
the three *regularity* fields `arcMaps_quadSep` (`quadSep` = condition (M5) of
`thm:scalar-lz-boundary`, uniform quadratic separation via a Heine–Cantor tube + Taylor +
compactness), `arcMaps_orientation` (`orientation` = the replica-symmetric half of (M2),
the supporting-line ⟺ convex-minorant dichotomy), and `arcMaps_noFlatTie` (`noFlatTie`,
the Lean-side window condition, Jensen via the strict supporting line + an ae→Dirac
argument), each consuming the global contact data via `A.gc`.

The `LZBoundaryArc` field labels used below are those of `LZBoundary/Arc.lean`, whose module
docstring gives the dictionary to conditions (M1)–(M5) of `thm:scalar-lz-boundary`.

`lem:convexity-defect` is *not* here: the convex–concave–convex structure of
`φ_{p,d}` — including the one-sided packagings `strictConvexOn_phi_left` /
`strictConvexOn_phi_right` used throughout this file — lives in `LZBoundary/PhiDeriv.lean`,
packaged as `convexity_defect`.
-/

namespace UpperTailOptimizers

open Real

/-- `φ''` is continuous on `(0,1)` (its formula is `hpd(rpow ·)/(d²(rpow ·)^(2d-1))`,
a quotient of continuous functions with nonvanishing denominator). -/
private theorem phi''_continuousOn {p : ℝ} {d : ℕ} (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (phi'' p d) (Set.Ioo 0 1) := by
  have hu : ContinuousOn (fun x => Real.rpow x (1 / (d:ℝ))) (Set.Ioo 0 1) := fun x hx =>
    (Real.continuousAt_rpow_const x (1 / (d:ℝ)) (Or.inl (ne_of_gt hx.1))).continuousWithinAt
  have humaps : Set.MapsTo (fun x => Real.rpow x (1 / (d:ℝ))) (Set.Ioo 0 1) (Set.Ioo 0 1) := by
    intro x hx
    refine ⟨Real.rpow_pos_of_pos hx.1 _, ?_⟩
    calc Real.rpow x (1 / (d:ℝ)) < Real.rpow 1 (1 / (d:ℝ)) :=
          Real.rpow_lt_rpow hx.1.le hx.2 (by positivity)
      _ = 1 := by simp
  have hnum : ContinuousOn (fun x => hpd p d (Real.rpow x (1 / (d:ℝ)))) (Set.Ioo 0 1) :=
    (hpd_continuousOn hd hp0 hp1).comp hu humaps
  have hden : ContinuousOn
      (fun x => (d:ℝ) ^ 2 * (Real.rpow x (1 / (d:ℝ))) ^ (2 * d - 1)) (Set.Ioo 0 1) :=
    continuousOn_const.mul (hu.pow _)
  have hdenne : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      (d:ℝ) ^ 2 * (Real.rpow x (1 / (d:ℝ))) ^ (2 * d - 1) ≠ 0 := by
    intro x hx
    have : 0 < Real.rpow x (1 / (d:ℝ)) := Real.rpow_pos_of_pos hx.1 _
    positivity
  exact hnum.div hden hdenne

open Filter Topology in
/-- **Detached wherever `φ` is concave.**  At any interior `x` with `φ''(x) < 0`, the
convex minorant lies strictly below `φ`: `φ` is strictly concave near `x`
(`strictConcaveOn_of_deriv2_neg`), so the strict-concave midpoint for `φ` beats the
convex midpoint for `lce` (with `lce ≤ φ`).  In particular `lce < φ` on the whole
concave region `(u_-^d, u_+^d)`. -/
private theorem lce_lt_phi_of_phi''_neg {d : ℕ} (hd : 2 ≤ d) {p x : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hx0 : 0 < x) (hx1 : x < 1) (hneg : phi'' p d x < 0) :
    lce 0 1 (phi p d) x < phi p d x := by
  have hf : ContinuousOn (phi p d) (Set.Icc 0 1) := phi_continuousOn_Icc hd hp0 hp1
  have hca : ContinuousAt (phi'' p d) x :=
    (phi''_continuousOn hd hp0 hp1).continuousAt (Ioo_mem_nhds hx0 hx1)
  have hmem : {y | phi'' p d y < 0} ∩ Set.Ioo (0:ℝ) 1 ∈ 𝓝 x :=
    Filter.inter_mem (hca (isOpen_Iio.mem_nhds hneg)) (Ioo_mem_nhds hx0 hx1)
  obtain ⟨η, hη0, hηsub⟩ := Metric.mem_nhds_iff.mp hmem
  set xl := x - η / 2 with hxl
  set xr := x + η / 2 with hxr
  have hl := hηsub (show xl ∈ Metric.ball x η by
    rw [Metric.mem_ball, Real.dist_eq, show xl - x = -(η / 2) from by rw [hxl]; ring,
      abs_neg, abs_of_pos (by linarith)]; linarith)
  have hr := hηsub (show xr ∈ Metric.ball x η by
    rw [Metric.mem_ball, Real.dist_eq, show xr - x = η / 2 from by rw [hxr]; ring,
      abs_of_pos (by linarith)]; linarith)
  have hsub01 : Set.Icc xl xr ⊆ Set.Ioo (0:ℝ) 1 := fun y hy =>
    ⟨lt_of_lt_of_le hl.2.1 hy.1, lt_of_le_of_lt hy.2 hr.2.2⟩
  have hconc : StrictConcaveOn ℝ (Set.Icc xl xr) (phi p d) := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
      (hf.mono (hsub01.trans Set.Ioo_subset_Icc_self))
    intro y hy
    rw [interior_Icc] at hy
    have hyIoo : y ∈ Set.Ioo (0:ℝ) 1 := hsub01 (Set.Ioo_subset_Icc_self hy)
    have hball : y ∈ Metric.ball x η := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1, hxl], by linarith [hy.2, hxr]⟩
    have hd2 : deriv (deriv (phi p d)) y = phi'' p d y :=
      (hasDerivAt_phi'' hd hp0 hp1 hyIoo.1 hyIoo.2).deriv
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rw [hd2]; exact (hηsub hball).1
  have hxlr : xl ≠ xr := by rw [hxl, hxr]; intro h; linarith
  have hmid : (1/2 : ℝ) • xl + (1/2 : ℝ) • xr = x := by
    rw [hxl, hxr]; simp only [smul_eq_mul]; ring
  have hconc_mid := hconc.2 (Set.left_mem_Icc.mpr (by linarith : xl ≤ xr))
    (Set.right_mem_Icc.mpr (by linarith : xl ≤ xr)) hxlr
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  rw [hmid] at hconc_mid
  have hxlIcc : xl ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hl.2
  have hxrIcc : xr ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hr.2
  have hconv_mid := (convexOn_lce (by norm_num) hf).2 hxlIcc hxrIcc
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  rw [hmid] at hconv_mid
  have hLl : lce 0 1 (phi p d) xl ≤ phi p d xl := lce_le_self (by norm_num) hf hxlIcc
  have hLr : lce 0 1 (phi p d) xr ≤ phi p d xr := lce_le_self (by norm_num) hf hxrIcc
  simp only [smul_eq_mul] at hconc_mid hconv_mid
  linarith [hconc_mid, hconv_mid, hLl, hLr]

/-- Non-emptiness of the detached set: at `x₀ = r_*^d` the convex minorant lies
strictly below `φ` (corollary of `lce_lt_phi_of_phi''_neg`, since `φ''(r_*^d) < 0`). -/
private theorem lce_lt_phi_at_rStar {d : ℕ} (hd : 2 ≤ d) {p : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) :
    lce 0 1 (phi p d) ((rStar d) ^ d) < phi p d ((rStar d) ^ d) := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  have hx₀0 : 0 < (rStar d) ^ d := pow_pos hus0 d
  have hx₀1 : (rStar d) ^ d < 1 := pow_lt_one₀ hus0.le hus1 (by omega)
  have hrp : Real.rpow ((rStar d) ^ d) (1 / (d:ℝ)) = rStar d := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hus0.le (by omega)
  have hφneg : phi'' p d ((rStar d) ^ d) < 0 := by
    rw [phi''_neg_iff hd hx₀0, hrp]; exact (hpd_rStar_neg_iff hd hp0 hp1).mpr hp
  exact lce_lt_phi_of_phi''_neg hd hp0 hp1 hx₀0 hx₀1 hφneg

/-- **Strict convexity defect at the left contact.**  A left contact `c` of the convex
minorant — `lce(c) = φ(c)` (`hLc`), tangent slope `m = φ'(c)` (`hmc`), and the tangent
line `t ↦ m t + (lce(c) − m c)` a global minorant (`hAmin`) — lying left of `r_*^d`
(`hcStar`) satisfies `c < u_-^d`, hence `h_{p,d}(c^{1/d}) > 0`.  Proof: `c ≤ u_-^d`
because a contact cannot lie in the concave region `(u_-^d,u_+^d)` (there `lce < φ`,
contradicting `lce(c)=φ(c)`); and `c ≠ u_-^d` because if `c = u_-^d` the tangent at `c`
lies strictly above the strictly-concave `φ` just to the right (MVT + `φ'` strictly
decreasing there), contradicting `hAmin`. -/
private theorem contact_left_hpd_pos {d : ℕ} (hd : 2 ≤ d) {p c m : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) (hc0 : 0 < c) (hcStar : c < (rStar d) ^ d)
    (hLc : lce 0 1 (phi p d) c = phi p d c)
    (hmc : deriv (phi p d) c = m)
    (hAmin : ∀ t ∈ Set.Icc (0:ℝ) 1, m * t + (lce 0 1 (phi p d) c - m * c) ≤ phi p d t) :
    0 < hpd p d (Real.rpow c (1/(d:ℝ))) := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hdne : d ≠ 0 := by omega
  have hzpos : (0:ℝ) < 1 / (d:ℝ) := by have := dpos hd; positivity
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  have hStarPow1 : (rStar d) ^ d < 1 := pow_lt_one₀ hus0.le hus1 hdne
  have hc1 : c < 1 := lt_trans hcStar hStarPow1
  obtain ⟨um, hum0, humStar, humzero, hum_pos⟩ := hpd_left_zero hd hp0 hp
  have humPow0 : (0:ℝ) < um ^ d := pow_pos hum0 d
  have humRp : Real.rpow (um ^ d) (1/(d:ℝ)) = um := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hum0.le hdne
  have hStarRp : Real.rpow ((rStar d) ^ d) (1/(d:ℝ)) = rStar d := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hus0.le hdne
  set a := Real.rpow c (1/(d:ℝ)) with hadef
  have ha0 : 0 < a := Real.rpow_pos_of_pos hc0 _
  have ha_lt_rStar : a < rStar d := by
    rw [hadef, ← hStarRp]; exact Real.rpow_lt_rpow hc0.le hcStar hzpos
  -- Part 1: `c ≤ u_-^d`.
  have hc_le : c ≤ um ^ d := by
    by_contra hcon
    push Not at hcon
    have ha_gt_um : um < a := by
      rw [hadef, ← humRp]; exact Real.rpow_lt_rpow humPow0.le hcon hzpos
    have hpd_neg : hpd p d a < 0 := by
      have := hpd_strictAntiOn hd hp0 hp1 ⟨hum0, humStar⟩ ⟨ha0, ha_lt_rStar⟩ ha_gt_um
      rwa [humzero] at this
    have hphi_neg : phi'' p d c < 0 := by
      rw [phi''_neg_iff hd hc0]; rw [← hadef]; exact hpd_neg
    have hlt := lce_lt_phi_of_phi''_neg hd hp0 hp1 hc0 hc1 hphi_neg
    rw [hLc] at hlt; exact lt_irrefl _ hlt
  -- Part 2: `c ≠ u_-^d`.
  have hc_ne : c ≠ um ^ d := by
    intro hceq
    set x := (c + (rStar d) ^ d) / 2 with hxdef
    have hcx : c < x := by rw [hxdef]; linarith [hcStar]
    have hx_lt : x < (rStar d) ^ d := by rw [hxdef]; linarith [hcStar]
    have hx0 : 0 < x := lt_trans hc0 hcx
    have hx1 : x < 1 := lt_trans hx_lt hStarPow1
    have hphi_neg : ∀ t ∈ Set.Ioo c x, phi'' p d t < 0 := by
      intro t ht
      have ht0 : 0 < t := lt_trans hc0 ht.1
      have htlt : t < (rStar d) ^ d := lt_trans ht.2 hx_lt
      have htumd : um ^ d < t := by rw [← hceq]; exact ht.1
      have htum : um < Real.rpow t (1/(d:ℝ)) := by
        rw [← humRp]; exact Real.rpow_lt_rpow humPow0.le htumd hzpos
      have htus : Real.rpow t (1/(d:ℝ)) < rStar d := by
        rw [← hStarRp]; exact Real.rpow_lt_rpow ht0.le htlt hzpos
      have htpos : 0 < Real.rpow t (1/(d:ℝ)) := Real.rpow_pos_of_pos ht0 _
      have hneg : hpd p d (Real.rpow t (1/(d:ℝ))) < 0 := by
        have := hpd_strictAntiOn hd hp0 hp1 ⟨hum0, humStar⟩ ⟨htpos, htus⟩ htum
        rwa [humzero] at this
      exact (phi''_neg_iff hd ht0).mpr hneg
    have hcontφ : ContinuousOn (phi p d) (Set.Icc c x) := fun y hy =>
      (hasDerivAt_phi hd hp0 hp1 (lt_of_lt_of_le hc0 hy.1)
        (lt_of_le_of_lt hy.2 hx1)).continuousAt.continuousWithinAt
    have hderivφ : ∀ y ∈ Set.Ioo c x, HasDerivAt (phi p d) (deriv (phi p d) y) y := by
      intro y hy
      have h := hasDerivAt_phi hd hp0 hp1 (lt_trans hc0 hy.1) (lt_trans hy.2 hx1)
      rw [h.deriv]; exact h
    obtain ⟨ξ, hξ, hξeq⟩ :=
      exists_hasDerivAt_eq_slope (phi p d) (deriv (phi p d)) hcx hcontφ hderivφ
    have hcont : ContinuousOn (deriv (phi p d)) (Set.Icc c x) := fun y hy =>
      (hasDerivAt_phi'' hd hp0 hp1 (lt_of_lt_of_le hc0 hy.1)
        (lt_of_le_of_lt hy.2 hx1)).continuousAt.continuousWithinAt
    have hanti : StrictAntiOn (deriv (phi p d)) (Set.Icc c x) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc c x) hcont
      intro y hy
      rw [interior_Icc] at hy
      have hd2 : deriv (deriv (phi p d)) y = phi'' p d y :=
        (hasDerivAt_phi'' hd hp0 hp1 (lt_trans hc0 hy.1) (lt_trans hy.2 hx1)).deriv
      rw [hd2]; exact hphi_neg y hy
    have hξm : deriv (phi p d) ξ < m := by
      have := hanti (Set.left_mem_Icc.mpr hcx.le) (Set.Ioo_subset_Icc_self hξ) hξ.1
      rwa [hmc] at this
    have hlt : phi p d x < phi p d c + m * (x - c) := by
      rw [hξeq, div_lt_iff₀ (by linarith : (0:ℝ) < x - c)] at hξm; linarith
    have hge : phi p d c + m * (x - c) ≤ phi p d x := by
      have h := hAmin x ⟨hx0.le, hx1.le⟩
      rw [hLc] at h
      have heq : m * x + (phi p d c - m * c) = phi p d c + m * (x - c) := by ring
      rw [heq] at h; exact h
    linarith [hlt, hge]
  have hc_lt : c < um ^ d := lt_of_le_of_ne hc_le hc_ne
  have ha_lt_um : a < um := by
    rw [hadef, ← humRp]; exact Real.rpow_lt_rpow hc0.le hc_lt hzpos
  exact hum_pos a ha0 ha_lt_um

/-- **Strict convexity defect at the right contact** (mirror of `contact_left_hpd_pos`).
A right contact `c` (lying right of `r_*^d`) of the convex minorant, with tangent slope
`m = φ'(c)` and tangent-line minorant, satisfies `c > u_+^d`, hence
`h_{p,d}(c^{1/d}) > 0`.  Same argument with `u_+`, strict monotonicity of `h` on
`(r_*,1)`, and the MVT just to the *left* of `c`. -/
private theorem contact_right_hpd_pos {d : ℕ} (hd : 2 ≤ d) {p c m : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) (hcStar : (rStar d) ^ d < c) (hc1 : c < 1)
    (hLc : lce 0 1 (phi p d) c = phi p d c)
    (hmc : deriv (phi p d) c = m)
    (hAmin : ∀ t ∈ Set.Icc (0:ℝ) 1, m * t + (lce 0 1 (phi p d) c - m * c) ≤ phi p d t) :
    0 < hpd p d (Real.rpow c (1/(d:ℝ))) := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hdne : d ≠ 0 := by omega
  have hzpos : (0:ℝ) < 1 / (d:ℝ) := by have := dpos hd; positivity
  have hus0 := rStar_pos hd
  have hStarPow0 : (0:ℝ) < (rStar d) ^ d := pow_pos hus0 d
  have hc0 : 0 < c := lt_trans hStarPow0 hcStar
  obtain ⟨up, hupStar, hup1, hupzero, hup_pos⟩ := hpd_right_zero hd hp0 hp
  have hup0 : 0 < up := lt_trans hus0 hupStar
  have hupPow0 : (0:ℝ) < up ^ d := pow_pos hup0 d
  have hupRp : Real.rpow (up ^ d) (1/(d:ℝ)) = up := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hup0.le hdne
  have hStarRp : Real.rpow ((rStar d) ^ d) (1/(d:ℝ)) = rStar d := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hus0.le hdne
  set a := Real.rpow c (1/(d:ℝ)) with hadef
  have ha0 : 0 < a := Real.rpow_pos_of_pos hc0 _
  have ha1 : a < 1 := by
    have h := Real.rpow_lt_rpow hc0.le hc1 hzpos
    rw [hadef]; simpa using h
  have ha_gt_rStar : rStar d < a := by
    rw [hadef, ← hStarRp]; exact Real.rpow_lt_rpow hStarPow0.le hcStar hzpos
  -- Part 1: `u_+^d ≤ c`.
  have hc_ge : up ^ d ≤ c := by
    by_contra hcon
    push Not at hcon
    have ha_lt_up : a < up := by
      rw [hadef, ← hupRp]; exact Real.rpow_lt_rpow hc0.le hcon hzpos
    have hpd_neg : hpd p d a < 0 := by
      have := hpd_strictMonoOn hd hp0 hp1 ⟨ha_gt_rStar, ha1⟩ ⟨hupStar, hup1⟩ ha_lt_up
      rwa [hupzero] at this
    have hphi_neg : phi'' p d c < 0 := by
      rw [phi''_neg_iff hd hc0]; rw [← hadef]; exact hpd_neg
    have hlt := lce_lt_phi_of_phi''_neg hd hp0 hp1 hc0 hc1 hphi_neg
    rw [hLc] at hlt; exact lt_irrefl _ hlt
  -- Part 2: `c ≠ u_+^d`.
  have hc_ne : c ≠ up ^ d := by
    intro hceq
    set x := ((rStar d) ^ d + c) / 2 with hxdef
    have hxc : x < c := by rw [hxdef]; linarith [hcStar]
    have hx_gt : (rStar d) ^ d < x := by rw [hxdef]; linarith [hcStar]
    have hx0 : 0 < x := lt_trans hStarPow0 hx_gt
    have hx1 : x < 1 := lt_trans hxc hc1
    have hphi_neg : ∀ t ∈ Set.Ioo x c, phi'' p d t < 0 := by
      intro t ht
      have ht0 : 0 < t := lt_trans hx0 ht.1
      have htgt : (rStar d) ^ d < t := lt_trans hx_gt ht.1
      have htupd : t < up ^ d := by rw [← hceq]; exact ht.2
      have htus : rStar d < Real.rpow t (1/(d:ℝ)) := by
        rw [← hStarRp]; exact Real.rpow_lt_rpow hStarPow0.le htgt hzpos
      have htup : Real.rpow t (1/(d:ℝ)) < up := by
        rw [← hupRp]; exact Real.rpow_lt_rpow ht0.le htupd hzpos
      have ht1 : Real.rpow t (1/(d:ℝ)) < 1 := lt_trans htup hup1
      have hneg : hpd p d (Real.rpow t (1/(d:ℝ))) < 0 := by
        have := hpd_strictMonoOn hd hp0 hp1 ⟨htus, ht1⟩ ⟨hupStar, hup1⟩ htup
        rwa [hupzero] at this
      exact (phi''_neg_iff hd ht0).mpr hneg
    have hcontφ : ContinuousOn (phi p d) (Set.Icc x c) := fun y hy =>
      (hasDerivAt_phi hd hp0 hp1 (lt_of_lt_of_le hx0 hy.1)
        (lt_of_le_of_lt hy.2 hc1)).continuousAt.continuousWithinAt
    have hderivφ : ∀ y ∈ Set.Ioo x c, HasDerivAt (phi p d) (deriv (phi p d) y) y := by
      intro y hy
      have h := hasDerivAt_phi hd hp0 hp1 (lt_trans hx0 hy.1) (lt_trans hy.2 hc1)
      rw [h.deriv]; exact h
    obtain ⟨ξ, hξ, hξeq⟩ :=
      exists_hasDerivAt_eq_slope (phi p d) (deriv (phi p d)) hxc hcontφ hderivφ
    have hcont : ContinuousOn (deriv (phi p d)) (Set.Icc x c) := fun y hy =>
      (hasDerivAt_phi'' hd hp0 hp1 (lt_of_lt_of_le hx0 hy.1)
        (lt_of_le_of_lt hy.2 hc1)).continuousAt.continuousWithinAt
    have hanti : StrictAntiOn (deriv (phi p d)) (Set.Icc x c) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc x c) hcont
      intro y hy
      rw [interior_Icc] at hy
      have hd2 : deriv (deriv (phi p d)) y = phi'' p d y :=
        (hasDerivAt_phi'' hd hp0 hp1 (lt_trans hx0 hy.1) (lt_trans hy.2 hc1)).deriv
      rw [hd2]; exact hphi_neg y hy
    have hξm : m < deriv (phi p d) ξ := by
      have := hanti (Set.Ioo_subset_Icc_self hξ) (Set.right_mem_Icc.mpr hxc.le) hξ.2
      rwa [hmc] at this
    have hlt : phi p d x < phi p d c + m * (x - c) := by
      rw [hξeq, lt_div_iff₀ (by linarith : (0:ℝ) < c - x)] at hξm
      nlinarith [hξm]
    have hge : phi p d c + m * (x - c) ≤ phi p d x := by
      have h := hAmin x ⟨hx0.le, hx1.le⟩
      rw [hLc] at h
      have heq : m * x + (phi p d c - m * c) = phi p d c + m * (x - c) := by ring
      rw [heq] at h; exact h
    linarith [hlt, hge]
  have hc_gt : up ^ d < c := lt_of_le_of_ne hc_ge (Ne.symm hc_ne)
  have ha_gt_up : up < a := by
    rw [hadef, ← hupRp]; exact Real.rpow_lt_rpow hupPow0.le hc_gt hzpos
  exact hup_pos a ha_gt_up ha1

/-- **Strict-convexity secant-vs-tangent inequality** for `φ_{p,d}`.  On an interval
`(A₁,A₂)` where `φ'' > 0`, the secant slope is strictly below the right-endpoint
tangent slope: `φ(A₂) − φ(A₁) < φ'(A₂)·(A₂ − A₁)`.  (MVT + `φ'` strictly increasing.) -/
private theorem phi_secant_lt_tangent {d : ℕ} (hd : 2 ≤ d) {p A₁ A₂ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (h1 : 0 < A₁) (h12 : A₁ < A₂) (h2 : A₂ < 1)
    (hconv : ∀ x ∈ Set.Ioo A₁ A₂, 0 < phi'' p d x) :
    phi p d A₂ - phi p d A₁ < deriv (phi p d) A₂ * (A₂ - A₁) := by
  have hcontφ : ContinuousOn (phi p d) (Set.Icc A₁ A₂) := fun y hy =>
    (hasDerivAt_phi hd hp0 hp1 (lt_of_lt_of_le h1 hy.1)
      (lt_of_le_of_lt hy.2 h2)).continuousAt.continuousWithinAt
  have hderivφ : ∀ y ∈ Set.Ioo A₁ A₂, HasDerivAt (phi p d) (deriv (phi p d) y) y := by
    intro y hy
    have h := hasDerivAt_phi hd hp0 hp1 (lt_trans h1 hy.1) (lt_trans hy.2 h2)
    rw [h.deriv]; exact h
  obtain ⟨ξ, hξ, hξeq⟩ :=
    exists_hasDerivAt_eq_slope (phi p d) (deriv (phi p d)) h12 hcontφ hderivφ
  have hcont : ContinuousOn (deriv (phi p d)) (Set.Icc A₁ A₂) := fun y hy =>
    (hasDerivAt_phi'' hd hp0 hp1 (lt_of_lt_of_le h1 hy.1)
      (lt_of_le_of_lt hy.2 h2)).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (deriv (phi p d)) (Set.Icc A₁ A₂) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc A₁ A₂) hcont
    intro y hy
    rw [interior_Icc] at hy
    have hd2 : deriv (deriv (phi p d)) y = phi'' p d y :=
      (hasDerivAt_phi'' hd hp0 hp1 (lt_trans h1 hy.1) (lt_trans hy.2 h2)).deriv
    rw [hd2]; exact hconv y hy
  have hξm : deriv (phi p d) ξ < deriv (phi p d) A₂ :=
    hmono (Set.Ioo_subset_Icc_self hξ) (Set.right_mem_Icc.mpr h12.le) hξ.2
  rw [hξeq, div_lt_iff₀ (by linarith : (0:ℝ) < A₂ - A₁)] at hξm
  linarith [hξm]

/-- **No two distinct constrained Lubetzky–Zhao contacts** (with `a₁ < a₂`).  Two
common-tangent pairs lying strictly outside the concave interval cannot have `a₁ < a₂`:
the two tangent lines `L₁` (at `a₁^d, b₁^d`) and `L₂` (at `a₂^d, b₂^d`) would satisfy
`L₂ > L₁` at `a₂^d` (`L₁` below the strictly-convex `φ` there) yet `L₂ < L₁` at `b₁^d`
(`L₂` below `φ` there), impossible for the steeper line `L₂` to the right of `a₂^d`. -/
private theorem contact_lt_false {d : ℕ} (hd : 2 ≤ d) {p a₁ b₁ a₂ b₂ : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d)
    (ha₁ : 0 < a₁) (ha₁s : a₁ < rStar d) (hb₁s : rStar d < b₁) (hb₁ : b₁ < 1)
    (hcf₁ : contactF d (a₁, b₁) p = 0) (hha₁ : 0 < hpd p d a₁) (hhb₁ : 0 < hpd p d b₁)
    (ha₂ : 0 < a₂) (ha₂s : a₂ < rStar d) (hb₂s : rStar d < b₂) (hb₂ : b₂ < 1)
    (hcf₂ : contactF d (a₂, b₂) p = 0) (hha₂ : 0 < hpd p d a₂) (hhb₂ : 0 < hpd p d b₂)
    (hlt : a₁ < a₂) : False := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hdR := dpos hd
  have hus0 := rStar_pos hd
  obtain ⟨um, hum0, humStar, humzero, hum_pos⟩ := hpd_left_zero hd hp0 hp
  obtain ⟨up, hupStar, hup1, hupzero, hup_pos⟩ := hpd_right_zero hd hp0 hp
  have hup0 : 0 < up := lt_trans hus0 hupStar
  have humRp : Real.rpow (um ^ d) (1/(d:ℝ)) = um := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hum0.le (by omega)
  have hupRp : Real.rpow (up ^ d) (1/(d:ℝ)) = up := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hup0.le (by omega)
  -- locate the contacts: a_i < u_-, b_i > u_+
  have hlt_um : ∀ a, 0 < a → a < rStar d → 0 < hpd p d a → a < um := fun a ha0 haus hha => by
    by_contra hcon; push Not at hcon
    have : hpd p d a ≤ hpd p d um := by
      rcases hcon.lt_or_eq with h | h
      · exact le_of_lt (hpd_strictAntiOn hd hp0 hp1 ⟨hum0, humStar⟩ ⟨ha0, haus⟩ h)
      · rw [h]
    rw [humzero] at this; linarith
  have hgt_up : ∀ b, b < 1 → rStar d < b → 0 < hpd p d b → up < b := fun b hb1' hbus hhb => by
    by_contra hcon; push Not at hcon
    have : hpd p d b ≤ hpd p d up := by
      rcases hcon.lt_or_eq with h | h
      · exact le_of_lt (hpd_strictMonoOn hd hp0 hp1 ⟨hbus, hb1'⟩ ⟨hupStar, hup1⟩ h)
      · rw [h]
    rw [hupzero] at this; linarith
  have ha₁um := hlt_um a₁ ha₁ ha₁s hha₁
  have ha₂um := hlt_um a₂ ha₂ ha₂s hha₂
  have hb₁up := hgt_up b₁ hb₁ hb₁s hhb₁
  have hb₂up := hgt_up b₂ hb₂ hb₂s hhb₂
  have hb₁0 : 0 < b₁ := lt_trans hus0 hb₁s
  have hb₂0 : 0 < b₂ := lt_trans hus0 hb₂s
  have ha₁1 : a₁ < 1 := lt_trans ha₁s (rStar_lt_one hd)
  have ha₂1 : a₂ < 1 := lt_trans ha₂s (rStar_lt_one hd)
  -- `φ'' > 0` on the two convex regions `(0,u_-^d)` and `(u_+^d,1)`
  have hposL : ∀ x ∈ Set.Ioo (0:ℝ) (um ^ d), 0 < phi'' p d x := by
    intro x hx
    rw [phi''_pos_iff hd hx.1]
    refine hum_pos _ (Real.rpow_pos_of_pos hx.1 _) ?_
    rw [← humRp]; exact Real.rpow_lt_rpow hx.1.le hx.2 (by positivity)
  have hposR : ∀ x ∈ Set.Ioo (up ^ d) (1:ℝ), 0 < phi'' p d x := by
    intro x hx
    have hx0 : 0 < x := lt_trans (pow_pos hup0 d) hx.1
    rw [phi''_pos_iff hd hx0]
    refine hup_pos _ ?_ ?_
    · rw [← hupRp]; exact Real.rpow_lt_rpow (pow_nonneg hup0.le d) hx.1 (by positivity)
    · have : Real.rpow x (1/(d:ℝ)) < Real.rpow 1 (1/(d:ℝ)) :=
        Real.rpow_lt_rpow hx0.le hx.2 (by positivity)
      simpa using this
  -- the common-tangent relations (slope + chord) in `φ`-coordinates for both solutions
  have tangent : ∀ a b : ℝ, 0 < a → a < 1 → 0 < b → b < 1 →
      contactF d (a, b) p = 0 →
      deriv (phi p d) (a ^ d) = deriv (phi p d) (b ^ d) ∧
      phi p d (b ^ d) - phi p d (a ^ d) = deriv (phi p d) (a ^ d) * (b ^ d - a ^ d) := by
    intro a b ha0 ha1 hb0' hb1' hcf
    have hsl : sCM d p a = sCM d p b := by
      have hx := (Prod.ext_iff.mp hcf).1; simp only [contactF, Prod.fst_zero] at hx; linarith
    have hch : Jp p b - Jp p a - sCM d p a * (b ^ d - a ^ d) = 0 := by
      have hx := (Prod.ext_iff.mp hcf).2; simpa only [contactF, Prod.snd_zero] using hx
    have hda : deriv (phi p d) (a ^ d) = sCM d p a := deriv_phi_pow_eq_sCM hd hp0 hp1 ha0 ha1
    have hdb : deriv (phi p d) (b ^ d) = sCM d p b := deriv_phi_pow_eq_sCM hd hp0 hp1 hb0' hb1'
    refine ⟨by rw [hda, hdb, hsl], ?_⟩
    rw [phi_pow_eq_Jp hd ha0, phi_pow_eq_Jp hd hb0', hda]; linarith
  obtain ⟨hsl₁, hchord₁⟩ := tangent a₁ b₁ ha₁ ha₁1 hb₁0 hb₁ hcf₁
  obtain ⟨hsl₂, hchord₂⟩ := tangent a₂ b₂ ha₂ ha₂1 hb₂0 hb₂ hcf₂
  -- membership of `a_i^d` and `b_i^d` in the convex regions
  have hA1mem : a₁ ^ d ∈ Set.Ioo (0:ℝ) (um ^ d) :=
    ⟨pow_pos ha₁ d, pow_lt_pow_left₀ ha₁um ha₁.le (by omega)⟩
  have hA2mem : a₂ ^ d ∈ Set.Ioo (0:ℝ) (um ^ d) :=
    ⟨pow_pos ha₂ d, pow_lt_pow_left₀ ha₂um ha₂.le (by omega)⟩
  have hB1mem : b₁ ^ d ∈ Set.Ioo (up ^ d) (1:ℝ) :=
    ⟨pow_lt_pow_left₀ hb₁up hup0.le (by omega), pow_lt_one₀ hb₁0.le hb₁ (by omega)⟩
  have hB2mem : b₂ ^ d ∈ Set.Ioo (up ^ d) (1:ℝ) :=
    ⟨pow_lt_pow_left₀ hb₂up hup0.le (by omega), pow_lt_one₀ hb₂0.le hb₂ (by omega)⟩
  have hA12 : a₁ ^ d < a₂ ^ d := pow_lt_pow_left₀ hlt ha₁.le (by omega)
  -- `φ'` is strictly increasing on each convex region
  have hmonoL : StrictMonoOn (deriv (phi p d)) (Set.Ioo 0 (um ^ d)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 (um ^ d))
    · intro y hy
      exact (hasDerivAt_phi'' hd hp0 hp1 hy.1
        (lt_trans hy.2 (pow_lt_one₀ hum0.le (lt_trans humStar (rStar_lt_one hd)) (by omega)))).continuousAt.continuousWithinAt
    · intro y hy; rw [interior_Ioo] at hy
      rw [(hasDerivAt_phi'' hd hp0 hp1 hy.1
        (lt_trans hy.2 (pow_lt_one₀ hum0.le (lt_trans humStar (rStar_lt_one hd)) (by omega)))).deriv]
      exact hposL y hy
  have hmonoR : StrictMonoOn (deriv (phi p d)) (Set.Ioo (up ^ d) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (up ^ d) 1)
    · intro y hy
      exact (hasDerivAt_phi'' hd hp0 hp1 (lt_trans (pow_pos hup0 d) hy.1) hy.2).continuousAt.continuousWithinAt
    · intro y hy; rw [interior_Ioo] at hy
      rw [(hasDerivAt_phi'' hd hp0 hp1 (lt_trans (pow_pos hup0 d) hy.1) hy.2).deriv]
      exact hposR y hy
  -- `m₁ < m₂` and `b₁^d < b₂^d`
  have hm12 : deriv (phi p d) (a₁ ^ d) < deriv (phi p d) (a₂ ^ d) := hmonoL hA1mem hA2mem hA12
  have hB12 : b₁ ^ d < b₂ ^ d := by
    have hderiv_b : deriv (phi p d) (b₁ ^ d) < deriv (phi p d) (b₂ ^ d) := by
      rw [← hsl₁, ← hsl₂]; exact hm12
    exact (hmonoR.lt_iff_lt hB1mem hB2mem).mp hderiv_b
  -- the two strict-convexity inequalities (the line geometry)
  have hP3 : deriv (phi p d) (a₁ ^ d) * (a₂ ^ d - a₁ ^ d)
      < phi p d (a₂ ^ d) - phi p d (a₁ ^ d) := by
    -- secant on `(A₁,A₂)` exceeds the LEFT tangent (`m₁`) — MVT + `φ'` increasing
    have hcontφ : ContinuousOn (phi p d) (Set.Icc (a₁ ^ d) (a₂ ^ d)) := fun y hy =>
      (hasDerivAt_phi hd hp0 hp1 (lt_of_lt_of_le hA1mem.1 hy.1)
        (lt_of_le_of_lt hy.2 (lt_trans hA2mem.2 (pow_lt_one₀ hum0.le (lt_trans humStar (rStar_lt_one hd)) (by omega))))).continuousAt.continuousWithinAt
    have hderivφ : ∀ y ∈ Set.Ioo (a₁ ^ d) (a₂ ^ d), HasDerivAt (phi p d) (deriv (phi p d) y) y := by
      intro y hy
      have h := hasDerivAt_phi hd hp0 hp1 (lt_trans hA1mem.1 hy.1)
        (lt_trans hy.2 (lt_trans hA2mem.2 (pow_lt_one₀ hum0.le (lt_trans humStar (rStar_lt_one hd)) (by omega))))
      rw [h.deriv]; exact h
    obtain ⟨ξ, hξ, hξeq⟩ :=
      exists_hasDerivAt_eq_slope (phi p d) (deriv (phi p d)) hA12 hcontφ hderivφ
    have hξmem : ξ ∈ Set.Ioo (0:ℝ) (um ^ d) := ⟨lt_trans hA1mem.1 hξ.1, lt_trans hξ.2 hA2mem.2⟩
    have hξm : deriv (phi p d) (a₁ ^ d) < deriv (phi p d) ξ := hmonoL hA1mem hξmem hξ.1
    rw [hξeq, lt_div_iff₀ (by linarith [hA12] : (0:ℝ) < a₂ ^ d - a₁ ^ d)] at hξm
    nlinarith [hξm]
  have hP2 : phi p d (b₂ ^ d) - phi p d (b₁ ^ d)
      < deriv (phi p d) (a₂ ^ d) * (b₂ ^ d - b₁ ^ d) := by
    have h := phi_secant_lt_tangent hd hp0 hp1 (lt_trans (pow_pos hup0 d) hB1mem.1) hB12 hB2mem.2
      (fun x hx => hposR x ⟨lt_trans hB1mem.1 hx.1, lt_trans hx.2 hB2mem.2⟩)
    rwa [← hsl₂] at h
  -- assemble the affine contradiction:  `D(b₁^d) - D(a₂^d) = (m₂-m₁)(b₁^d-a₂^d)`
  have hBA : a₂ ^ d < b₁ ^ d :=
    lt_trans hA2mem.2 (lt_trans (pow_lt_pow_left₀ (lt_trans humStar hupStar) hum0.le (by omega)) hB1mem.1)
  nlinarith [hP3, hP2, hchord₁, hchord₂, hm12, hBA,
    mul_pos (sub_pos.mpr hm12) (sub_pos.mpr hBA)]

/-- **Per-`p` uniqueness of the constrained Lubetzky–Zhao contact pair.** -/
private theorem contact_unique {d : ℕ} (hd : 2 ≤ d) {p a₁ b₁ a₂ b₂ : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d)
    (ha₁ : 0 < a₁) (ha₁s : a₁ < rStar d) (hb₁s : rStar d < b₁) (hb₁ : b₁ < 1)
    (hcf₁ : contactF d (a₁, b₁) p = 0) (hha₁ : 0 < hpd p d a₁) (hhb₁ : 0 < hpd p d b₁)
    (ha₂ : 0 < a₂) (ha₂s : a₂ < rStar d) (hb₂s : rStar d < b₂) (hb₂ : b₂ < 1)
    (hcf₂ : contactF d (a₂, b₂) p = 0) (hha₂ : 0 < hpd p d a₂) (hhb₂ : 0 < hpd p d b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have haeq : a₁ = a₂ := by
    rcases lt_trichotomy a₁ a₂ with h | h | h
    · exact (contact_lt_false hd hp0 hp ha₁ ha₁s hb₁s hb₁ hcf₁ hha₁ hhb₁
        ha₂ ha₂s hb₂s hb₂ hcf₂ hha₂ hhb₂ h).elim
    · exact h
    · exact (contact_lt_false hd hp0 hp ha₂ ha₂s hb₂s hb₂ hcf₂ hha₂ hhb₂
        ha₁ ha₁s hb₁s hb₁ hcf₁ hha₁ hhb₁ h).elim
  refine ⟨haeq, ?_⟩
  -- equal `a` ⟹ equal slope ⟹ equal `b` (slope strictly increasing on the right region)
  have hsl₁ : sCM d p a₁ = sCM d p b₁ := by
    have hx := (Prod.ext_iff.mp hcf₁).1; simp only [contactF, Prod.fst_zero] at hx; linarith
  have hsl₂ : sCM d p a₂ = sCM d p b₂ := by
    have hx := (Prod.ext_iff.mp hcf₂).1; simp only [contactF, Prod.fst_zero] at hx; linarith
  obtain ⟨up, hupStar, hup1, hupzero, hup_pos⟩ := hpd_right_zero hd hp0 hp
  have hup0 : 0 < up := lt_trans (rStar_pos hd) hupStar
  have hgt_up : ∀ b, b < 1 → rStar d < b → 0 < hpd p d b → up < b := fun b hb1' hbus hhb => by
    by_contra hcon; push Not at hcon
    have : hpd p d b ≤ hpd p d up := by
      rcases hcon.lt_or_eq with h | h
      · exact le_of_lt (hpd_strictMonoOn hd hp0 hp1 ⟨hbus, hb1'⟩ ⟨hupStar, hup1⟩ h)
      · rw [h]
    rw [hupzero] at this; linarith
  have hb₁up := hgt_up b₁ hb₁ hb₁s hhb₁
  have hb₂up := hgt_up b₂ hb₂ hb₂s hhb₂
  have hb₁0 : 0 < b₁ := lt_trans (rStar_pos hd) hb₁s
  have hb₂0 : 0 < b₂ := lt_trans (rStar_pos hd) hb₂s
  have hupRp : Real.rpow (up ^ d) (1/(d:ℝ)) = up := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hup0.le (by omega)
  have hposR : ∀ x ∈ Set.Ioo (up ^ d) (1:ℝ), 0 < phi'' p d x := by
    intro x hx
    have hx0 : 0 < x := lt_trans (pow_pos hup0 d) hx.1
    rw [phi''_pos_iff hd hx0]
    refine hup_pos _ ?_ ?_
    · rw [← hupRp]; exact Real.rpow_lt_rpow (pow_nonneg hup0.le d) hx.1 (by have := dpos hd; positivity)
    · have : Real.rpow x (1/(d:ℝ)) < Real.rpow 1 (1/(d:ℝ)) :=
        Real.rpow_lt_rpow hx0.le hx.2 (by have := dpos hd; positivity)
      simpa using this
  have hmonoR : StrictMonoOn (deriv (phi p d)) (Set.Ioo (up ^ d) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (up ^ d) 1)
    · intro y hy
      exact (hasDerivAt_phi'' hd hp0 hp1 (lt_trans (pow_pos hup0 d) hy.1) hy.2).continuousAt.continuousWithinAt
    · intro y hy; rw [interior_Ioo] at hy
      rw [(hasDerivAt_phi'' hd hp0 hp1 (lt_trans (pow_pos hup0 d) hy.1) hy.2).deriv]
      exact hposR y hy
  -- `sCM a₁ = sCM a₂` (since `a₁ = a₂`) ⟹ `sCM b₁ = sCM b₂` ⟹ `deriv φ` equal at `b_i^d`
  have hsleq : deriv (phi p d) (b₁ ^ d) = deriv (phi p d) (b₂ ^ d) := by
    rw [deriv_phi_pow_eq_sCM hd hp0 hp1 hb₁0 hb₁, deriv_phi_pow_eq_sCM hd hp0 hp1 hb₂0 hb₂,
      ← hsl₁, ← hsl₂, haeq]
  have hB1mem : b₁ ^ d ∈ Set.Ioo (up ^ d) (1:ℝ) :=
    ⟨pow_lt_pow_left₀ hb₁up hup0.le (by omega), pow_lt_one₀ hb₁0.le hb₁ (by omega)⟩
  have hB2mem : b₂ ^ d ∈ Set.Ioo (up ^ d) (1:ℝ) :=
    ⟨pow_lt_pow_left₀ hb₂up hup0.le (by omega), pow_lt_one₀ hb₂0.le hb₂ (by omega)⟩
  have hBeq : b₁ ^ d = b₂ ^ d := hmonoR.injOn hB1mem hB2mem hsleq
  rcases lt_trichotomy b₁ b₂ with h | h | h
  · exact absurd hBeq (ne_of_lt (pow_lt_pow_left₀ h hb₁0.le (by omega)))
  · exact h
  · exact absurd hBeq.symm (ne_of_lt (pow_lt_pow_left₀ h hb₂0.le (by omega)))

open Filter Topology in
/-- The detached-component extraction underlying `lem:contact-points`.

(i) Non-empty: at `x₀ = r_*^d`,
`φ''(x₀) < 0` (`phi''_neg_iff` + `hpd_rStar_neg_iff`, both proved) and `φ''` is
continuous (`phi''_continuousOn`, proved above), so `φ` is strictly concave near
`x₀` (`strictConcaveOn_of_deriv2_neg`); the strict-concave midpoint for `φ` and the
convex midpoint for `lce` (with `lce ≤ φ`) give `lce x₀ < φ x₀`.  (ii) Component
`(c,d')` = (sup of left contacts, inf of right contacts) around `x₀`: closed sets,
so `c,d'` are contacts with `c < x₀ < d'` and `lce < φ` on `(c,d')`.  (iii) `0 < c`,
`d' < 1` from `φ' → ∓∞` at the endpoints (`phi'_tendsto_atBot`/`phi'_tendsto_atTop`,
proved) + MVT, since an affine piece of `lce` has finite slope.  All ingredients
exist (`ConvexMinorant.lean`, `PhiDeriv.lean`, `phi''_continuousOn`); this is the
remaining topological assembly. -/
private theorem exists_lz_boundary_component {d : ℕ} (hd : 2 ≤ d) {p : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) :
    ∃ c d' : ℝ, 0 < c ∧ c < d' ∧ d' < 1 ∧
      c < (rStar d) ^ d ∧ (rStar d) ^ d < d' ∧
      lce 0 1 (phi p d) c = phi p d c ∧ lce 0 1 (phi p d) d' = phi p d d' ∧
      ∀ x ∈ Set.Ioo c d', lce 0 1 (phi p d) x < phi p d x := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hf : ContinuousOn (phi p d) (Set.Icc 0 1) := phi_continuousOn_Icc hd hp0 hp1
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  set x₀ := (rStar d) ^ d with hx₀def
  have hx₀0 : 0 < x₀ := by rw [hx₀def]; positivity
  have hx₀1 : x₀ < 1 := by rw [hx₀def]; exact pow_lt_one₀ hus0.le hus1 (by omega)
  have hx₀mem : x₀ ∈ Set.Ioo (0:ℝ) 1 := ⟨hx₀0, hx₀1⟩
  have hlt : lce 0 1 (phi p d) x₀ < phi p d x₀ := lce_lt_phi_at_rStar hd hp0 hp
  obtain ⟨c, hc0, hcx₀, hLc, hcomp_l⟩ := exists_left_contact (by norm_num) hf hx₀mem hlt
  obtain ⟨d', hx₀d', hd'1, hLd', hcomp_r⟩ := exists_right_contact (by norm_num) hf hx₀mem hlt
  -- `lce < φ` on the whole component `(c, d')`
  have hcomp : ∀ x ∈ Set.Ioo c d', lce 0 1 (phi p d) x < phi p d x := by
    intro x hx
    rcases lt_trichotomy x x₀ with h | h | h
    · exact hcomp_l x ⟨hx.1, h⟩
    · rw [h]; exact hlt
    · exact hcomp_r x ⟨h, hx.2⟩
  -- `0 < c`: were `c = 0`, `lce` would be affine on `(0,d')` with intercept `φ 0`,
  -- but the slope is finite while `φ' → -∞` at `0` (MVT contradiction).
  have hc0' : 0 < c := by
    rcases hc0.lt_or_eq with hc_pos | hc_eq
    · exact hc_pos
    · exfalso
      subst hc_eq
      have hd'0 : (0:ℝ) < d' := hx₀0.trans hx₀d'
      obtain ⟨s, hs⟩ := lce_eq_affine_left (show (0:ℝ) < 1 by norm_num) hf hd'0
        hd'1 hcomp
      have hev : ∀ᶠ y in 𝓝[>] (0:ℝ), deriv (phi p d) y < s :=
        (phi'_tendsto_atBot hd hp0 hp1).eventually (eventually_lt_atBot s)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
      obtain ⟨δ, hδ0, hδ⟩ := hev
      set x₁ := min (d' / 2) (δ / 2) with hx₁def
      have hx₁0 : 0 < x₁ := lt_min (by linarith) (by linarith)
      have hx₁d' : x₁ < d' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hx₁δ : x₁ < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hx₁1 : x₁ < 1 := lt_of_lt_of_le hx₁d' hd'1
      have hx₁mem : x₁ ∈ Set.Ioo (0:ℝ) d' := ⟨hx₁0, hx₁d'⟩
      have hx₁Icc : x₁ ∈ Set.Icc (0:ℝ) 1 := ⟨hx₁0.le, hx₁1.le⟩
      have hge : phi p d 0 + s * (x₁ - 0) ≤ phi p d x₁ := by
        have h1 := hs x₁ hx₁mem
        have h2 := lce_le_self (show (0:ℝ) ≤ 1 by norm_num) hf hx₁Icc
        rw [h1] at h2; exact h2
      have hcont : ContinuousOn (phi p d) (Set.Icc 0 x₁) :=
        hf.mono (Set.Icc_subset_Icc le_rfl hx₁1.le)
      have hderiv : ∀ y ∈ Set.Ioo (0:ℝ) x₁, HasDerivAt (phi p d) (deriv (phi p d) y) y := by
        intro y hy
        have h := hasDerivAt_phi hd hp0 hp1 hy.1 (lt_trans hy.2 hx₁1)
        rw [h.deriv]; exact h
      obtain ⟨ξ, hξ, hξeq⟩ :=
        exists_hasDerivAt_eq_slope (phi p d) (deriv (phi p d)) hx₁0 hcont hderiv
      have hξδ : deriv (phi p d) ξ < s := by
        have hdist : dist ξ (0:ℝ) < δ := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hξ.1]; exact lt_trans hξ.2 hx₁δ
        exact hδ hdist (Set.mem_Ioi.mpr hξ.1)
      have hslope : s ≤ (phi p d x₁ - phi p d 0) / (x₁ - 0) := by
        rw [le_div_iff₀ (show (0:ℝ) < x₁ - 0 by linarith)]; linarith [hge]
      rw [hξeq] at hξδ
      linarith [hslope, hξδ]
  -- `d' < 1`: symmetric, using `φ' → +∞` at `1`.
  have hd'1' : d' < 1 := by
    rcases hd'1.lt_or_eq with hd'_lt | hd'_eq
    · exact hd'_lt
    · exfalso
      subst hd'_eq
      have hc1 : c < 1 := hcx₀.trans hx₀d'
      obtain ⟨s, hs⟩ := lce_eq_affine_right (show (0:ℝ) < 1 by norm_num) hf hc1 hc0 hcomp
      have hev : ∀ᶠ y in 𝓝[<] (1:ℝ), s < deriv (phi p d) y :=
        (phi'_tendsto_atTop hd hp0 hp1).eventually (eventually_gt_atTop s)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
      obtain ⟨δ, hδ0, hδ⟩ := hev
      set x₁ := max ((c + 1) / 2) (1 - δ / 2) with hx₁def
      have hx₁1 : x₁ < 1 := max_lt (by linarith) (by linarith)
      have hx₁c : c < x₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hx₁lb : 1 - δ / 2 ≤ x₁ := le_max_right _ _
      have hx₁0 : 0 < x₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hx₁mem : x₁ ∈ Set.Ioo c 1 := ⟨hx₁c, hx₁1⟩
      have hx₁Icc : x₁ ∈ Set.Icc (0:ℝ) 1 := ⟨hx₁0.le, hx₁1.le⟩
      have hge : phi p d 1 + s * (x₁ - 1) ≤ phi p d x₁ := by
        have h1 := hs x₁ hx₁mem
        have h2 := lce_le_self (show (0:ℝ) ≤ 1 by norm_num) hf hx₁Icc
        rw [h1] at h2; exact h2
      have hcont : ContinuousOn (phi p d) (Set.Icc x₁ 1) :=
        hf.mono (Set.Icc_subset_Icc hx₁0.le le_rfl)
      have hderiv : ∀ y ∈ Set.Ioo x₁ (1:ℝ), HasDerivAt (phi p d) (deriv (phi p d) y) y := by
        intro y hy
        have h := hasDerivAt_phi hd hp0 hp1 (lt_trans hx₁0 hy.1) hy.2
        rw [h.deriv]; exact h
      obtain ⟨ξ, hξ, hξeq⟩ :=
        exists_hasDerivAt_eq_slope (phi p d) (deriv (phi p d)) hx₁1 hcont hderiv
      have hξδ : s < deriv (phi p d) ξ := by
        have hdist : dist ξ (1:ℝ) < δ := by
          rw [Real.dist_eq, abs_of_nonpos (show ξ - 1 ≤ 0 by linarith [hξ.2])]
          have : 1 - δ / 2 < ξ := lt_of_le_of_lt hx₁lb hξ.1
          linarith
        exact hδ hdist (Set.mem_Iio.mpr hξ.2)
      have hsx : s * (1 - x₁) = -(s * (x₁ - 1)) := by ring
      have hslope : (phi p d 1 - phi p d x₁) / (1 - x₁) ≤ s := by
        rw [div_le_iff₀ (show (0:ℝ) < 1 - x₁ by linarith)]; linarith [hge, hsx]
      rw [hξeq] at hξδ
      linarith [hslope, hξδ]
  exact ⟨c, d', hc0', hcx₀.trans hx₀d', hd'1', hcx₀, hx₀d', hLc, hLd', hcomp⟩

/-- **`lem:contact-points`.**  For `0 < p < p_*` there are two contact
points `x_a < x_b` in `(0,1)` at which the one-variable graph `φ_{p,d}` shares a
common tangent line: the slopes agree and the chord equals that slope.  Proved
via the convex minorant of `φ_{p,d}` on `[0,1]`. -/
theorem lz_boundary_contacts {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp : p < pStar d) :
    ∃ xa xb : ℝ, 0 < xa ∧ xa < xb ∧ xb < 1 ∧
      deriv (phi p d) xa = deriv (phi p d) xb ∧
      phi p d xb - phi p d xa = deriv (phi p d) xa * (xb - xa) ∧
      xa < (rStar d) ^ d ∧ (rStar d) ^ d < xb ∧
      0 < hpd p d (Real.rpow xa (1/(d:ℝ))) ∧ 0 < hpd p d (Real.rpow xb (1/(d:ℝ))) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, phi p d xa + deriv (phi p d) xa * (x - xa) ≤ phi p d x) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, phi p d xb + deriv (phi p d) xb * (x - xb) ≤ phi p d x) ∧
      lce 0 1 (phi p d) xa = phi p d xa ∧
      lce 0 1 (phi p d) xb = phi p d xb ∧
      (∀ x ∈ Set.Ioo xa xb, lce 0 1 (phi p d) x < phi p d x) := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hf : ContinuousOn (phi p d) (Set.Icc 0 1) := phi_continuousOn_Icc hd hp0 hp1
  obtain ⟨c, d', hc0, hcd', hd'1, hcStar, hStarD, hLc, hLd', hcomp⟩ :=
    exists_lz_boundary_component hd hp0 hp
  set L := lce 0 1 (phi p d) with hLdef
  have hdc'pos : (0:ℝ) < d' - c := by linarith
  have hdc'ne : d' - c ≠ 0 := ne_of_gt hdc'pos
  set m : ℝ := (L d' - L c) / (d' - c) with hm
  have hc01 : c ∈ Set.Icc (0:ℝ) 1 := ⟨hc0.le, le_trans hcd'.le hd'1.le⟩
  have hd01 : d' ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hc0.le hcd'.le, hd'1.le⟩
  have hc_ioo : c ∈ Set.Ioo (0:ℝ) 1 := ⟨hc0, lt_trans hcd' hd'1⟩
  have hd_ioo : d' ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_trans hc0 hcd', hd'1⟩
  -- `L` is affine on `[c,d']`
  have haff : ∀ x ∈ Set.Icc c d', L x = L c + m * (x - c) :=
    lce_affine_on_component hf hcd' hc0 hd'1 hcomp hLc hLd'
  -- the chord `A(t) = m·t + (L c - m·c)` is an affine minorant of `φ` on `[0,1]`
  have hAmin : ∀ t ∈ Set.Icc (0:ℝ) 1, m * t + (L c - m * c) ≤ phi p d t := by
    intro t ht
    have hLt : L t ≤ phi p d t := lce_le_self (by norm_num) hf ht
    by_cases htin : t ∈ Set.Icc c d'
    · have heq : m * t + (L c - m * c) = L t := by rw [haff t htin]; ring
      rw [heq]; exact hLt
    · have htout : t < c ∨ d' < t := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at htin; tauto
      have hch : L c + m * (t - c) ≤ L t := chord_le_lce_outside (by norm_num) hf hcd' hc01 hd01 ht htout
      have heq : m * t + (L c - m * c) = L c + m * (t - c) := by ring
      rw [heq]; exact le_trans hch hLt
  -- tangency at the two contacts
  have htouch_c : m * c + (L c - m * c) = phi p d c := by rw [← hLc]; ring
  have hmdc : m * (d' - c) = L d' - L c := by rw [hm]; field_simp
  have htouch_d : m * d' + (L c - m * c) = phi p d d' := by rw [← hLd']; linear_combination hmdc
  have hVc := hasDerivAt_phi hd hp0 hp1 hc_ioo.1 hc_ioo.2
  have hVd := hasDerivAt_phi hd hp0 hp1 hd_ioo.1 hd_ioo.2
  have hmc : deriv (phi p d) c = m := by
    rw [hVc.deriv]; exact tangent_of_affineMinorant hAmin hc_ioo htouch_c hVc
  have hmd : deriv (phi p d) d' = m := by
    rw [hVd.deriv]; exact tangent_of_affineMinorant hAmin hd_ioo htouch_d hVd
  -- strict convexity defect at the two contacts (contacts strictly outside `(u_-,u_+)`)
  have hLc' : lce 0 1 (phi p d) c = phi p d c := by have h := hLc; rwa [hLdef] at h
  have hLd'' : lce 0 1 (phi p d) d' = phi p d d' := by have h := hLd'; rwa [hLdef] at h
  have hAmin' : ∀ t ∈ Set.Icc (0:ℝ) 1,
      m * t + (lce 0 1 (phi p d) c - m * c) ≤ phi p d t := by
    intro t ht; have h := hAmin t ht; rwa [hLdef] at h
  -- the same affine line, written with the intercept at `d'` (equal via `htouch_d`)
  have hAmin'' : ∀ t ∈ Set.Icc (0:ℝ) 1,
      m * t + (lce 0 1 (phi p d) d' - m * d') ≤ phi p d t := by
    have hint : lce 0 1 (phi p d) d' - m * d' = lce 0 1 (phi p d) c - m * c := by
      have ht2 := htouch_d; rw [hLdef] at ht2; linarith [ht2, hLd'']
    intro t ht; rw [hint]; exact hAmin' t ht
  have hhpa : 0 < hpd p d (Real.rpow c (1/(d:ℝ))) :=
    contact_left_hpd_pos hd hp0 hp hc0 hcStar hLc' hmc hAmin'
  have hhpb : 0 < hpd p d (Real.rpow d' (1/(d:ℝ))) :=
    contact_right_hpd_pos hd hp0 hp hStarD hd'1 hLd'' hmd hAmin''
  -- supporting-line minorants at the two contacts (the same affine line, written
  -- as a tangent at `c` and at `d'`)
  have hsupp_c : ∀ x ∈ Set.Icc (0:ℝ) 1,
      phi p d c + deriv (phi p d) c * (x - c) ≤ phi p d x := by
    intro x hx
    have h := hAmin x hx
    rw [hmc]
    have heq : phi p d c + m * (x - c) = m * x + (L c - m * c) := by
      rw [← htouch_c]; ring
    rw [heq]; exact h
  have hsupp_d : ∀ x ∈ Set.Icc (0:ℝ) 1,
      phi p d d' + deriv (phi p d) d' * (x - d') ≤ phi p d x := by
    intro x hx
    have h := hAmin x hx
    rw [hmd]
    have heq : phi p d d' + m * (x - d') = m * x + (L c - m * c) := by
      rw [← htouch_d]; ring
    rw [heq]; exact h
  refine ⟨c, d', hc0, hcd', hd'1, hmc.trans hmd.symm, ?_, hcStar, hStarD, hhpa, hhpb,
    hsupp_c, hsupp_d, hLc', hLd'', hcomp⟩
  rw [hmc]
  -- chord equation `φ d' - φ c = m (d' - c)`
  have : phi p d d' - phi p d c = m * (d' - c) := by
    rw [← htouch_d, ← htouch_c]; ring
  linarith [this]

open Filter Topology in
/-- **`lem:contact-point-limits`.**  Writing `u_a(p) = x_a(p)^{1/d}`,
`u_b(p) = x_b(p)^{1/d}` for the Lubetzky–Zhao contacts of `lem:contact-points`, as `p ↑ p_*` both
tend to `r_* = (d-1)/d`, while as `p ↓ 0` we have `u_a → 0` and `u_b → 1`.

Stated relative to contact functions `ua, ub : (0,p_*) → (0,1)` satisfying the
common-tangent equations of `lem:contact-points`.  We additionally record that the contacts
lie in the **convex** region of `φ_{p,d}`, i.e. `h_{p,d}(u_a) ≥ 0` and
`h_{p,d}(u_b) ≥ 0` (equivalently `φ_{p,d}'' ≥ 0` at `x_a`, `x_b`).  This is part
of `lem:contact-points`'s construction (the contacts bound the concave interval), and it is
exactly the structure the paper uses to rule out the degenerate `p↓0` limit
`u_a, u_b → r_*`: the abstract common-tangent equations alone are consistent with
that spurious limit at leading order in `log(1/p)`, so the convexity sign is
needed (and faithful). -/
theorem lz_boundary_endpoint_limits {d : ℕ} (hd : 2 ≤ d)
    (ua ub : ℝ → ℝ)
    (hcontacts : ∀ p, 0 < p → p < pStar d →
      0 < ua p ∧ ua p < rStar d ∧ rStar d < ub p ∧ ub p < 1 ∧
      deriv (phi p d) ((ua p) ^ d) = deriv (phi p d) ((ub p) ^ d) ∧
      phi p d ((ub p) ^ d) - phi p d ((ua p) ^ d)
        = deriv (phi p d) ((ua p) ^ d) * ((ub p) ^ d - (ua p) ^ d) ∧
      0 ≤ hpd p d (ua p) ∧ 0 ≤ hpd p d (ub p)) :
    Filter.Tendsto ua (nhdsWithin (pStar d) (Set.Iio (pStar d))) (nhds (rStar d)) ∧
    Filter.Tendsto ub (nhdsWithin (pStar d) (Set.Iio (pStar d))) (nhds (rStar d)) ∧
    Filter.Tendsto ua (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto ub (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hps0 : 0 < pStar d := pStar_pos hd
  have hps1 : pStar d < 1 := pStar_lt_one hd
  have hus0 : 0 < rStar d := rStar_pos hd
  have hus1 : rStar d < 1 := rStar_lt_one hd
  have hd0 : d ≠ 0 := by omega
  -- eventually `0 < p < p_*` on each one-sided filter
  have hev_lt : ∀ᶠ p in 𝓝[<] (pStar d), 0 < p ∧ p < pStar d := by
    have h1 : ∀ᶠ p in 𝓝[<] (pStar d), p < pStar d := self_mem_nhdsWithin
    have h2 : ∀ᶠ p in 𝓝[<] (pStar d), 0 < p :=
      eventually_nhdsWithin_of_eventually_nhds
        (Filter.eventually_of_mem (Ioi_mem_nhds hps0) (fun x hx => hx))
    exact h2.and h1
  have hev_gt : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < p ∧ p < pStar d := by
    have h1 : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < p := self_mem_nhdsWithin
    have h2 : ∀ᶠ p in 𝓝[>] (0:ℝ), p < pStar d :=
      eventually_nhdsWithin_of_eventually_nhds
        (Filter.eventually_of_mem (Iio_mem_nhds hps0) (fun x hx => hx))
    exact h1.and h2
  -- eventual membership in compact intervals
  have hf_lt : ∀ᶠ p in 𝓝[<] (pStar d), ua p ∈ Set.Icc (0:ℝ) (rStar d) := by
    filter_upwards [hev_lt] with p h
    obtain ⟨h1, h2, _⟩ := hcontacts p h.1 h.2; exact ⟨h1.le, h2.le⟩
  have hg_lt : ∀ᶠ p in 𝓝[<] (pStar d), ub p ∈ Set.Icc (rStar d) 1 := by
    filter_upwards [hev_lt] with p h
    obtain ⟨_, _, h3, h4, _⟩ := hcontacts p h.1 h.2; exact ⟨h3.le, h4.le⟩
  have hf_gt : ∀ᶠ p in 𝓝[>] (0:ℝ), ua p ∈ Set.Icc (0:ℝ) (rStar d) := by
    filter_upwards [hev_gt] with p h
    obtain ⟨h1, h2, _⟩ := hcontacts p h.1 h.2; exact ⟨h1.le, h2.le⟩
  have hg_gt : ∀ᶠ p in 𝓝[>] (0:ℝ), ub p ∈ Set.Icc (rStar d) 1 := by
    filter_upwards [hev_gt] with p h
    obtain ⟨_, _, h3, h4, _⟩ := hcontacts p h.1 h.2; exact ⟨h3.le, h4.le⟩
  ------------------------------------------------------------------
  -- Part 1: `p ↑ p_*`  (both contacts → r_*)
  ------------------------------------------------------------------
  have part1 := tendsto_pair_of_subseq (l := 𝓝[<] (pStar d)) (f := ua) (g := ub)
      (a := 0) (b := rStar d) (A := rStar d) (B := 1) (a₀ := rStar d) (b₀ := rStar d)
      hf_lt hg_lt (by
    intro u α β hu hua hub
    have hups : Tendsto u atTop (𝓝 (pStar d)) := hu.mono_right nhdsWithin_le_nhds
    have hupos : ∀ᶠ n in atTop, 0 < u n ∧ u n < pStar d := hu.eventually hev_lt
    have hpn : ∀ᶠ n in atTop, 0 < u n ∧ u n < 1 :=
      hupos.mono (fun n h => ⟨h.1, lt_trans h.2 hps1⟩)
    have hua_mem : ∀ᶠ n in atTop, ua (u n) ∈ Set.Icc (0:ℝ) (rStar d) := hu.eventually hf_lt
    have hub_mem : ∀ᶠ n in atTop, ub (u n) ∈ Set.Icc (rStar d) 1 := hu.eventually hg_lt
    have hα0 : 0 ≤ α := ge_of_tendsto hua (hua_mem.mono fun n h => h.1)
    have hαus : α ≤ rStar d := le_of_tendsto hua (hua_mem.mono fun n h => h.2)
    have hβus : rStar d ≤ β := ge_of_tendsto hub (hub_mem.mono fun n h => h.1)
    have hβ1 : β ≤ 1 := le_of_tendsto hub (hub_mem.mono fun n h => h.2)
    have hβpos : 0 < β := lt_of_lt_of_le hus0 hβus
    have hxan : ∀ᶠ n in atTop, 0 < (ua (u n)) ^ d ∧ (ua (u n)) ^ d < 1 := by
      filter_upwards [hupos] with n h
      obtain ⟨h1, h2, _⟩ := hcontacts (u n) h.1 h.2
      exact ⟨pow_pos h1 d, pow_lt_one₀ h1.le (lt_trans h2 hus1) hd0⟩
    have hxbn : ∀ᶠ n in atTop, 0 < (ub (u n)) ^ d ∧ (ub (u n)) ^ d < 1 := by
      filter_upwards [hupos] with n h
      obtain ⟨_, _, h3, h4, _⟩ := hcontacts (u n) h.1 h.2
      exact ⟨pow_pos (lt_trans hus0 h3) d, pow_lt_one₀ (lt_trans hus0 h3).le h4 hd0⟩
    have hslope_ev : (fun n => deriv (phi (u n) d) ((ua (u n)) ^ d)) =ᶠ[atTop]
        (fun n => deriv (phi (u n) d) ((ub (u n)) ^ d)) := by
      filter_upwards [hupos] with n h
      obtain ⟨_, _, _, _, hs, _⟩ := hcontacts (u n) h.1 h.2
      exact hs
    have hxa : Tendsto (fun n => (ua (u n)) ^ d) atTop (𝓝 (α ^ d)) :=
      ((continuous_pow d).tendsto α).comp hua
    have hxb : Tendsto (fun n => (ub (u n)) ^ d) atTop (𝓝 (β ^ d)) :=
      ((continuous_pow d).tendsto β).comp hub
    -- rule out α = 0
    have hαpos : 0 < α := by
      rcases hα0.lt_or_eq with h | h
      · exact h
      · exfalso
        have hxa0 : Tendsto (fun n => (ua (u n)) ^ d) atTop (𝓝 0) := by
          have hc := hxa; rw [← h, zero_pow hd0] at hc; exact hc
        have hLHS := phi_deriv_tendsto_atBot_joint hd hps0 hps1 hups hxa0 hpn hxan
        have hRHS : Tendsto (fun n => deriv (phi (u n) d) ((ub (u n)) ^ d)) atTop atBot :=
          hLHS.congr' hslope_ev
        rcases hβ1.lt_or_eq with hβlt | hβeq
        · have hβd1 : β ^ d < 1 := pow_lt_one₀ hβpos.le hβlt hd0
          have hcont := phi_deriv_jointContinuous hd hps0 hps1 (pow_pos hβpos d) hβd1
            hups hxb hpn hxbn
          exact not_tendsto_nhds_of_tendsto_atBot hRHS _ hcont
        · have hxb1 : Tendsto (fun n => (ub (u n)) ^ d) atTop (𝓝 1) := by
            have hc := hxb; rw [hβeq, one_pow] at hc; exact hc
          have hRHS' := phi_deriv_tendsto_atTop_joint hd hps0 hps1 hups hxb1 hpn hxbn
          exact (hRHS.not_tendsto disjoint_atBot_atTop) hRHS'
    -- rule out β = 1
    have hβlt1 : β < 1 := by
      rcases hβ1.lt_or_eq with h | h
      · exact h
      · exfalso
        have hxb1 : Tendsto (fun n => (ub (u n)) ^ d) atTop (𝓝 1) := by
          have hc := hxb; rw [h, one_pow] at hc; exact hc
        have hRHS := phi_deriv_tendsto_atTop_joint hd hps0 hps1 hups hxb1 hpn hxbn
        have hLHS : Tendsto (fun n => deriv (phi (u n) d) ((ua (u n)) ^ d)) atTop atTop :=
          hRHS.congr' hslope_ev.symm
        have hαd1 : α ^ d < 1 := pow_lt_one₀ hαpos.le (lt_of_le_of_lt hαus hus1) hd0
        have hcont := phi_deriv_jointContinuous hd hps0 hps1 (pow_pos hαpos d) hαd1
          hups hxa hpn hxan
        exact not_tendsto_nhds_of_tendsto_atTop hLHS _ hcont
    -- now `0 < α ≤ r_* ≤ β < 1`; pass the slope equation to the limit
    have hαd1 : α ^ d < 1 := pow_lt_one₀ hαpos.le (lt_of_le_of_lt hαus hus1) hd0
    have hβd1 : β ^ d < 1 := pow_lt_one₀ hβpos.le hβlt1 hd0
    have hLa := phi_deriv_jointContinuous hd hps0 hps1 (pow_pos hαpos d) hαd1 hups hxa hpn hxan
    have hLb := phi_deriv_jointContinuous hd hps0 hps1 (pow_pos hβpos d) hβd1 hups hxb hpn hxbn
    have hval : deriv (phi (pStar d) d) (α ^ d) = deriv (phi (pStar d) d) (β ^ d) :=
      tendsto_nhds_unique (hLa.congr' hslope_ev) hLb
    have hαβd : α ^ d = β ^ d :=
      (phi_deriv_pStar_strictMonoOn hd).injOn ⟨pow_pos hαpos d, hαd1⟩ ⟨pow_pos hβpos d, hβd1⟩ hval
    have hαβ : α = β := by
      rcases lt_trichotomy α β with h | h | h
      · exact absurd hαβd (ne_of_lt (pow_lt_pow_left₀ h hαpos.le hd0))
      · exact h
      · exact absurd hαβd.symm (ne_of_lt (pow_lt_pow_left₀ h hβpos.le hd0))
    have hαeq : α = rStar d := le_antisymm hαus (by rw [hαβ]; exact hβus)
    exact ⟨hαeq, by rw [← hαβ]; exact hαeq⟩)
  ------------------------------------------------------------------
  -- Part 2: `p ↓ 0`  (`u_a → 0`, `u_b → 1`)
  ------------------------------------------------------------------
  have part2 := tendsto_pair_of_subseq (l := 𝓝[>] (0:ℝ)) (f := ua) (g := ub)
      (a := 0) (b := rStar d) (A := rStar d) (B := 1) (a₀ := 0) (b₀ := 1)
      hf_gt hg_gt (by
    intro u α β hu hua hub
    have hupos : ∀ᶠ n in atTop, 0 < u n ∧ u n < pStar d := hu.eventually hev_gt
    have hua_mem : ∀ᶠ n in atTop, ua (u n) ∈ Set.Icc (0:ℝ) (rStar d) := hu.eventually hf_gt
    have hub_mem : ∀ᶠ n in atTop, ub (u n) ∈ Set.Icc (rStar d) 1 := hu.eventually hg_gt
    have hα0 : 0 ≤ α := ge_of_tendsto hua (hua_mem.mono fun n h => h.1)
    have hαus : α ≤ rStar d := le_of_tendsto hua (hua_mem.mono fun n h => h.2)
    have hβus : rStar d ≤ β := ge_of_tendsto hub (hub_mem.mono fun n h => h.1)
    have hβ1 : β ≤ 1 := le_of_tendsto hub (hub_mem.mono fun n h => h.2)
    have hua01 : ∀ᶠ n in atTop, 0 < ua (u n) ∧ ua (u n) < 1 := by
      filter_upwards [hupos] with n h
      obtain ⟨h1, h2, _⟩ := hcontacts (u n) h.1 h.2
      exact ⟨h1, lt_trans h2 hus1⟩
    have hub01 : ∀ᶠ n in atTop, 0 < ub (u n) ∧ ub (u n) < 1 := by
      filter_upwards [hupos] with n h
      obtain ⟨_, _, h3, h4, _⟩ := hcontacts (u n) h.1 h.2
      exact ⟨lt_trans hus0 h3, h4⟩
    refine ⟨?_, ?_⟩
    · -- α = 0
      by_contra hαne
      have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hαne)
      have hα1 : α < 1 := lt_of_le_of_lt hαus hus1
      have hbot := hpd_tendsto_atBot_p_zero hd hαpos hα1 hu hua hua01
      have hge0 : ∀ᶠ n in atTop, 0 ≤ hpd (u n) d (ua (u n)) := by
        filter_upwards [hupos] with n h
        obtain ⟨_, _, _, _, _, _, hca, _⟩ := hcontacts (u n) h.1 h.2
        exact hca
      obtain ⟨n, hge, hlt⟩ := (hge0.and (hbot.eventually_lt_atBot 0)).exists
      exact absurd hge (not_le.mpr hlt)
    · -- β = 1
      by_contra hβne
      have hβlt1 : β < 1 := lt_of_le_of_ne hβ1 hβne
      have hβpos : 0 < β := lt_of_lt_of_le hus0 hβus
      have hbot := hpd_tendsto_atBot_p_zero hd hβpos hβlt1 hu hub hub01
      have hge0 : ∀ᶠ n in atTop, 0 ≤ hpd (u n) d (ub (u n)) := by
        filter_upwards [hupos] with n h
        obtain ⟨_, _, _, _, _, _, _, hcb⟩ := hcontacts (u n) h.1 h.2
        exact hcb
      obtain ⟨n, hge, hlt⟩ := (hge0.and (hbot.eventually_lt_atBot 0)).exists
      exact absurd hge (not_le.mpr hlt))
  exact ⟨part1.1, part1.2, part2.1, part2.2⟩

/-!
## `thm:scalar-lz-boundary`: assembly scaffold

The proof of `thm:scalar-lz-boundary` is split into precisely-stated,
individually faithful sub-lemmas (the "`exists_lz_boundary_component`" pattern of
`lem:contact-points`).  The
structure `ArcMaps d r₀` packages the *construction* half — the parameter
interval `U ∋ r₀` (avoiding the exceptional density `r_*`), the analytic boundary
curve `pc` and second-contact map `sm`, and the three "shallow" `LZBoundaryArc` fields
`ordering`, `supporting`, `secondContact` that follow directly from Lemmas 3.3–3.4
(existence, analyticity, and the common-tangent / supporting-line / second-contact
equations).  The three *regularity* fields `quadSep`, `orientation`, `noFlatTie` are
supplied separately by `arcMaps_quadSep`, `arcMaps_orientation`, `arcMaps_noFlatTie`,
each consuming an `ArcMaps`.

`scalar_lz_boundary_arcs` then assembles the `LZBoundaryArc` record and discharges
non-exceptionality, so the theorem decomposes into the four proved sub-obligations
`exists_arcMaps`, `arcMaps_quadSep`, `arcMaps_orientation`, `arcMaps_noFlatTie`.
-/

open Filter Topology in
/-- **Global Lubetzky–Zhao contact data — the keystone of the Lean proof of `thm:scalar-lz-boundary`.**  The two contact
maps `u_a, u_b : (0,p_*) → (0,1)` of Lemmas 3.3–3.4, packaged as *single-valued*
real-analytic functions: on `(0,p_*)` they are ordered `0 < u_a < r_* < u_b < 1`,
solve the `u`-coordinate contact system `contactF d (u_a,u_b) p = 0` (equal slope +
chord), have strict convexity defect `0 < h_{p,d}` at both contacts (so the
non-degeneracy hypotheses of `contacts_analytic`/`contact_deriv_*` hold), are
analytic and strictly monotone (`u_a` increasing, `u_b` decreasing), and carry the
Lemma-4.4 endpoint limits.  This is the shared layer that both the construction
(`arcMaps_of_globalContacts`) and the regularity conditions (M4–M6) consume. -/
structure GlobalContacts (d : ℕ) where
  /-- Left Lubetzky–Zhao contact `u_a(p)` (u-coordinate). -/
  ua : ℝ → ℝ
  /-- Right Lubetzky–Zhao contact `u_b(p)` (u-coordinate). -/
  ub : ℝ → ℝ
  /-- On `(0,p_*)`: ordering, the contact system, and strict convexity at the contacts. -/
  contact : ∀ p, 0 < p → p < pStar d →
    0 < ua p ∧ ua p < rStar d ∧ rStar d < ub p ∧ ub p < 1 ∧
      contactF d (ua p, ub p) p = 0 ∧
      0 < hpd p d (ua p) ∧ 0 < hpd p d (ub p)
  analytic_ua : ∀ p, 0 < p → p < pStar d → AnalyticAt ℝ ua p
  analytic_ub : ∀ p, 0 < p → p < pStar d → AnalyticAt ℝ ub p
  mono_ua : StrictMonoOn ua (Set.Ioo 0 (pStar d))
  mono_ub : StrictAntiOn ub (Set.Ioo 0 (pStar d))
  /-- The contact maps move with strictly positive / negative speed (`dx_a/dp > 0`,
  `dx_b/dp < 0`); the pointwise form of `mono_ua`/`mono_ub`, needed for the local
  inverse (`p_c` analytic) and the `orientation` field. -/
  deriv_ua_pos : ∀ p, 0 < p → p < pStar d → 0 < deriv ua p
  deriv_ub_neg : ∀ p, 0 < p → p < pStar d → deriv ub p < 0
  /-- The supporting-line minorant of the Lubetzky–Zhao graph `x ↦ φ_{p,d}` at the
  left contact `x_a = u_a(p)^d` (the tangent line lies below the graph on `[0,1]`). -/
  support_ua : ∀ p, 0 < p → p < pStar d → ∀ x ∈ Set.Icc (0:ℝ) 1,
    phi p d ((ua p) ^ d) + deriv (phi p d) ((ua p) ^ d) * (x - (ua p) ^ d) ≤ phi p d x
  /-- The supporting-line minorant at the right contact `x_b = u_b(p)^d`. -/
  support_ub : ∀ p, 0 < p → p < pStar d → ∀ x ∈ Set.Icc (0:ℝ) 1,
    phi p d ((ub p) ^ d) + deriv (phi p d) ((ub p) ^ d) * (x - (ub p) ^ d) ≤ phi p d x
  ua_lim_pStar : Tendsto ua (𝓝[<] (pStar d)) (𝓝 (rStar d))
  ub_lim_pStar : Tendsto ub (𝓝[<] (pStar d)) (𝓝 (rStar d))
  ua_lim_zero : Tendsto ua (𝓝[>] (0:ℝ)) (𝓝 0)
  ub_lim_zero : Tendsto ub (𝓝[>] (0:ℝ)) (𝓝 1)

namespace GlobalContacts

variable {d : ℕ} (G : GlobalContacts d)

/-- The left contact map is continuous on `(0,p_*)` (from analyticity). -/
theorem continuousOn_ua : ContinuousOn G.ua (Set.Ioo 0 (pStar d)) := fun p hp =>
  (G.analytic_ua p hp.1 hp.2).continuousAt.continuousWithinAt

/-- The right contact map is continuous on `(0,p_*)` (from analyticity). -/
theorem continuousOn_ub : ContinuousOn G.ub (Set.Ioo 0 (pStar d)) := fun p hp =>
  (G.analytic_ub p hp.1 hp.2).continuousAt.continuousWithinAt

/-- The left contact map is injective on `(0,p_*)` (from strict monotonicity). -/
theorem injOn_ua : Set.InjOn G.ua (Set.Ioo 0 (pStar d)) := G.mono_ua.injOn

/-- The right contact map is injective on `(0,p_*)` (from strict antitonicity). -/
theorem injOn_ub : Set.InjOn G.ub (Set.Ioo 0 (pStar d)) := G.mono_ub.injOn

open Filter Topology in
/-- Eventually-in-`(0,p_*)` near each endpoint of the parameter interval. -/
private theorem eventually_Ioo_zero {d : ℕ} (hd : 2 ≤ d) :
    (∀ᶠ p in 𝓝[>] (0:ℝ), 0 < p ∧ p < pStar d) ∧
    (∀ᶠ p in 𝓝[<] (pStar d), 0 < p ∧ p < pStar d) := by
  have hps0 : 0 < pStar d := pStar_pos hd
  refine ⟨?_, ?_⟩
  · have h1 : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < p := self_mem_nhdsWithin
    have h2 : ∀ᶠ p in 𝓝[>] (0:ℝ), p < pStar d :=
      eventually_nhdsWithin_of_eventually_nhds
        (Filter.eventually_of_mem (Iio_mem_nhds hps0) (fun _ hx => hx))
    exact h1.and h2
  · have h1 : ∀ᶠ p in 𝓝[<] (pStar d), 0 < p :=
      eventually_nhdsWithin_of_eventually_nhds
        (Filter.eventually_of_mem (Ioi_mem_nhds hps0) (fun _ hx => hx))
    have h2 : ∀ᶠ p in 𝓝[<] (pStar d), p < pStar d := self_mem_nhdsWithin
    exact h1.and h2

open Filter Topology in
/-- The left contact map is surjective onto `(0,r_*)` (continuous + strictly increasing,
with the `lem:contact-point-limits` endpoint limits `u_a→0` and `u_a→r_*`; IVT). -/
theorem surjOn_ua (hd : 2 ≤ d) : Set.SurjOn G.ua (Set.Ioo 0 (pStar d)) (Set.Ioo 0 (rStar d)) := by
  obtain ⟨hev_gt, hev_lt⟩ := eventually_Ioo_zero hd
  intro y hy
  have hua_lt : ∀ᶠ p in 𝓝[>] (0:ℝ), G.ua p < y := G.ua_lim_zero (Iio_mem_nhds hy.1)
  have hua_gt : ∀ᶠ p in 𝓝[<] (pStar d), y < G.ua p := G.ua_lim_pStar (Ioi_mem_nhds hy.2)
  obtain ⟨p₁, hp₁lt, hp₁0, hp₁ps⟩ := (hua_lt.and hev_gt).exists
  obtain ⟨p₂, hp₂gt, hp₂0, hp₂ps⟩ := (hua_gt.and hev_lt).exists
  have hp₁p₂ : p₁ < p₂ := (G.mono_ua.lt_iff_lt ⟨hp₁0, hp₁ps⟩ ⟨hp₂0, hp₂ps⟩).mp (lt_trans hp₁lt hp₂gt)
  have hsub : Set.Icc p₁ p₂ ⊆ Set.Ioo 0 (pStar d) := fun x hx =>
    ⟨lt_of_lt_of_le hp₁0 hx.1, lt_of_le_of_lt hx.2 hp₂ps⟩
  obtain ⟨p, hpmem, hpy⟩ :=
    intermediate_value_Ioo hp₁p₂.le (G.continuousOn_ua.mono hsub) ⟨hp₁lt, hp₂gt⟩
  exact ⟨p, ⟨lt_trans hp₁0 hpmem.1, lt_trans hpmem.2 hp₂ps⟩, hpy⟩

open Filter Topology in
/-- The right contact map is surjective onto `(r_*,1)` (continuous + strictly decreasing,
with the `lem:contact-point-limits` endpoint limits `u_b→1` and `u_b→r_*`; IVT). -/
theorem surjOn_ub (hd : 2 ≤ d) : Set.SurjOn G.ub (Set.Ioo 0 (pStar d)) (Set.Ioo (rStar d) 1) := by
  obtain ⟨hev_gt, hev_lt⟩ := eventually_Ioo_zero hd
  intro y hy
  have hub_gt : ∀ᶠ p in 𝓝[>] (0:ℝ), y < G.ub p := G.ub_lim_zero (Ioi_mem_nhds hy.2)
  have hub_lt : ∀ᶠ p in 𝓝[<] (pStar d), G.ub p < y := G.ub_lim_pStar (Iio_mem_nhds hy.1)
  obtain ⟨p₁, hp₁gt, hp₁0, hp₁ps⟩ := (hub_gt.and hev_gt).exists
  obtain ⟨p₂, hp₂lt, hp₂0, hp₂ps⟩ := (hub_lt.and hev_lt).exists
  have hp₁p₂ : p₁ < p₂ := by
    by_contra hcon; push Not at hcon
    rcases hcon.lt_or_eq with h | h
    · have := G.mono_ub ⟨hp₂0, hp₂ps⟩ ⟨hp₁0, hp₁ps⟩ h; linarith [hp₂lt, hp₁gt]
    · rw [h] at hp₂lt; linarith [hp₂lt, hp₁gt]
  have hsub : Set.Icc p₁ p₂ ⊆ Set.Ioo 0 (pStar d) := fun x hx =>
    ⟨lt_of_lt_of_le hp₁0 hx.1, lt_of_le_of_lt hx.2 hp₂ps⟩
  obtain ⟨p, hpmem, hpy⟩ :=
    intermediate_value_Ioo' hp₁p₂.le (G.continuousOn_ub.mono hsub) ⟨hp₂lt, hp₁gt⟩
  exact ⟨p, ⟨lt_trans hp₁0 hpmem.1, lt_trans hpmem.2 hp₂ps⟩, hpy⟩

end GlobalContacts

/-- **The per-`p` Lubetzky–Zhao contact base solution** (the full `GlobalContacts.contact`
data).  For `p ∈ (0,p_*)` there are `0 < a < r_* < b < 1` with `contactF d (a,b) p = 0`
and strict convexity defect `0 < h_{p,d}(a)`, `0 < h_{p,d}(b)`.  Built from the
strengthened `lz_boundary_contacts` (straddle + `0<h` at the contacts via
`contact_left_hpd_pos`/`contact_right_hpd_pos`) through the coordinate bridge
`contactF_of_phi_contacts`.  This is exactly the pointwise data the keystone
`GlobalContacts.contact` field requires (the globalisation — single-valuedness,
analyticity, monotonicity, endpoint limits — is `exists_globalContacts` below). -/
theorem exists_contactF_zero {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp : p < pStar d) :
    ∃ a b : ℝ, 0 < a ∧ a < rStar d ∧ rStar d < b ∧ b < 1 ∧ contactF d (a, b) p = 0 ∧
      0 < hpd p d a ∧ 0 < hpd p d b ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1,
        phi p d (a ^ d) + deriv (phi p d) (a ^ d) * (x - a ^ d) ≤ phi p d x) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1,
        phi p d (b ^ d) + deriv (phi p d) (b ^ d) * (x - b ^ d) ≤ phi p d x) := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  obtain ⟨xa, xb, hxa0, hab, hxb1, hslope, hchord, hxaStar, hStarXb, hhpa, hhpb,
      hsupp_a, hsupp_b, _, _, _⟩ := lz_boundary_contacts hd hp0 hp
  have hzpos : (0:ℝ) < 1 / (d:ℝ) := by have := dpos hd; positivity
  have hStarEq : Real.rpow ((rStar d) ^ d) (1/(d:ℝ)) = rStar d := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast (rStar_pos hd).le (by omega)
  have hpow_a : (Real.rpow xa (1/(d:ℝ))) ^ d = xa := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hxa0.le (by omega)
  have hpow_b : (Real.rpow xb (1/(d:ℝ))) ^ d = xb := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow (lt_trans hxa0 hab).le (by omega)
  refine ⟨Real.rpow xa (1/(d:ℝ)), Real.rpow xb (1/(d:ℝ)),
    Real.rpow_pos_of_pos hxa0 _, ?_, ?_, ?_,
    contactF_of_phi_contacts hd hp0 hp1 hxa0 hab hxb1 hslope hchord, hhpa, hhpb,
    ?_, ?_⟩
  · -- `a = x_a^{1/d} < r_*`
    rw [← hStarEq]; exact Real.rpow_lt_rpow hxa0.le hxaStar hzpos
  · -- `r_* < x_b^{1/d} = b`
    rw [← hStarEq]; exact Real.rpow_lt_rpow (pow_nonneg (rStar_pos hd).le d) hStarXb hzpos
  · -- `b < 1`
    have hb1 : Real.rpow xb (1/(d:ℝ)) < Real.rpow 1 (1/(d:ℝ)) :=
      Real.rpow_lt_rpow (lt_trans hxa0 hab).le hxb1 hzpos
    simpa using hb1
  · -- supporting line at `a^d = x_a`
    rw [hpow_a]; exact hsupp_a
  · -- supporting line at `b^d = x_b`
    rw [hpow_b]; exact hsupp_b

/-- `p ↦ h_{p,d}(g p)` is continuous at `p₀` when `g` is continuous there with
`g p₀ ∈ (0,1)` and `p₀ ∈ (0,1)` (the building block for the eventual `0 < h` along the
local contact family). -/
private theorem hpd_comp_continuousAt {d : ℕ} {p₀ : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousAt g p₀) (hp00 : 0 < p₀) (hp01 : p₀ < 1)
    (hg0 : 0 < g p₀) (hg1 : g p₀ < 1) :
    ContinuousAt (fun p => hpd p d (g p)) p₀ := by
  have hgne : g p₀ ≠ 0 := ne_of_gt hg0
  have h1gne : (1:ℝ) - g p₀ ≠ 0 := by linarith
  have hp0ne : p₀ ≠ 0 := ne_of_gt hp00
  have hcont_1mg : ContinuousAt (fun p => 1 - g p) p₀ := by fun_prop
  have hcont_1mp : ContinuousAt (fun p : ℝ => 1 - p) p₀ := by fun_prop
  have heq : (fun p => hpd p d (g p)) =
      fun p => g p * (1 / (g p * (1 - g p)))
        - ((d:ℝ) - 1) * Real.log (g p * (1 - p) / ((1 - g p) * p)) := by
    funext p; rw [hpd, Jp'', Jp']
  rw [heq]
  refine ContinuousAt.sub ?_ ?_
  · exact hg.mul (continuousAt_const.div (hg.mul hcont_1mg) (mul_ne_zero hgne h1gne))
  · refine continuousAt_const.mul (ContinuousAt.log ?_ ?_)
    · exact (hg.mul hcont_1mp).div (hcont_1mg.mul continuousAt_id) (mul_ne_zero h1gne hp0ne)
    · have : (0:ℝ) < g p₀ * (1 - p₀) / ((1 - g p₀) * p₀) :=
        div_pos (mul_pos hg0 (by linarith)) (mul_pos (by linarith) hp00)
      exact ne_of_gt this

open Filter Topology in
/-- **The keystone of the Lean proof of `thm:scalar-lz-boundary`.**  The global single-valued analytic monotone
Lubetzky–Zhao contact maps exist.  We pick, for each `p ∈ (0,p_*)`, the base solution
`(u_a(p), u_b(p))` of `exists_contactF_zero` (via `Classical.choose`).  The
`GlobalContacts` conditions are proved as follows: `contact` (directly), the
endpoint limits `ua/ub_lim_*` (`lem:contact-point-limits` `lz_boundary_endpoint_limits`, after
converting `contactF = 0` to the `φ'`-form via the `x^d`-bridges),
`mono_ua`/`mono_ub` (`contact_deriv_ua_pos`/`contact_deriv_ub_neg`
+ `strictMonoOn_of_deriv_pos`), and the **analyticity** of the chosen contacts
(`hanalytic`), by identifying the `Classical.choose` contacts with the local
analytic solution of `contacts_analytic` near each `p₀` — the local
implicit-function uniqueness/continuity step (`contact_unique`). -/
theorem exists_globalContacts {d : ℕ} (hd : 2 ≤ d) : Nonempty (GlobalContacts d) := by
  classical
  have hps1 : pStar d < 1 := pStar_lt_one hd
  have hus1 : rStar d < 1 := rStar_lt_one hd
  have hus0 : 0 < rStar d := rStar_pos hd
  -- single-valued contact maps from the per-`p` base solution
  obtain ⟨ua, ub, spec⟩ : ∃ ua ub : ℝ → ℝ, ∀ p, 0 < p → p < pStar d →
      0 < ua p ∧ ua p < rStar d ∧ rStar d < ub p ∧ ub p < 1 ∧
      contactF d (ua p, ub p) p = 0 ∧ 0 < hpd p d (ua p) ∧ 0 < hpd p d (ub p) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1,
        phi p d ((ua p) ^ d) + deriv (phi p d) ((ua p) ^ d) * (x - (ua p) ^ d) ≤ phi p d x) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1,
        phi p d ((ub p) ^ d) + deriv (phi p d) ((ub p) ^ d) * (x - (ub p) ^ d) ≤ phi p d x) := by
    refine ⟨fun p => if h : 0 < p ∧ p < pStar d then
              (exists_contactF_zero hd h.1 h.2).choose else 0,
            fun p => if h : 0 < p ∧ p < pStar d then
              (exists_contactF_zero hd h.1 h.2).choose_spec.choose else 0, ?_⟩
    intro p hp0 hp
    simp only [dif_pos (⟨hp0, hp⟩ : 0 < p ∧ p < pStar d)]
    exact (exists_contactF_zero hd hp0 hp).choose_spec.choose_spec
  -- the slope equation `sCM(ua) = sCM(ub)` from `contactF = 0`
  have slopeEq : ∀ p, 0 < p → p < pStar d → sCM d p (ua p) = sCM d p (ub p) := by
    intro p hp0 hp
    obtain ⟨_, _, _, _, h5, _, _, _, _⟩ := spec p hp0 hp
    have hx := (Prod.ext_iff.mp h5).1
    simp only [contactF, Prod.fst_zero] at hx; linarith [hx]
  -- endpoint limits via `lem:contact-point-limits`
  have hcontacts : ∀ p, 0 < p → p < pStar d →
      0 < ua p ∧ ua p < rStar d ∧ rStar d < ub p ∧ ub p < 1 ∧
      deriv (phi p d) ((ua p) ^ d) = deriv (phi p d) ((ub p) ^ d) ∧
      phi p d ((ub p) ^ d) - phi p d ((ua p) ^ d)
        = deriv (phi p d) ((ua p) ^ d) * ((ub p) ^ d - (ua p) ^ d) ∧
      0 ≤ hpd p d (ua p) ∧ 0 ≤ hpd p d (ub p) := by
    intro p hp0 hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, _, _⟩ := spec p hp0 hp
    have hp1 : p < 1 := lt_trans hp hps1
    have hua1 : ua p < 1 := lt_trans h2 hus1
    have hub0 : 0 < ub p := lt_trans hus0 h3
    have hch : Jp p (ub p) - Jp p (ua p)
        - sCM d p (ua p) * ((ub p) ^ d - (ua p) ^ d) = 0 := by
      have hx := (Prod.ext_iff.mp h5).2; simpa only [contactF, Prod.snd_zero] using hx
    have hda : deriv (phi p d) ((ua p) ^ d) = sCM d p (ua p) :=
      deriv_phi_pow_eq_sCM hd hp0 hp1 h1 hua1
    have hdb : deriv (phi p d) ((ub p) ^ d) = sCM d p (ub p) :=
      deriv_phi_pow_eq_sCM hd hp0 hp1 hub0 h4
    have hpa : phi p d ((ua p) ^ d) = Jp p (ua p) := phi_pow_eq_Jp hd h1
    have hpb : phi p d ((ub p) ^ d) = Jp p (ub p) := phi_pow_eq_Jp hd hub0
    refine ⟨h1, h2, h3, h4, by rw [hda, hdb]; exact slopeEq p hp0 hp, ?_, h6.le, h7.le⟩
    rw [hpa, hpb, hda]; linarith [hch]
  obtain ⟨lim1, lim2, lim3, lim4⟩ := lz_boundary_endpoint_limits hd ua ub hcontacts
  -- analyticity: identify the chosen contacts with the local `contacts_analytic` solution
  have hanalytic : ∀ p, 0 < p → p < pStar d → AnalyticAt ℝ ua p ∧ AnalyticAt ℝ ub p := by
    intro p₀ hp₀0 hp₀
    obtain ⟨ha0, has, hbs, hb1, hcf0, hha0, hhb0, _, _⟩ := spec p₀ hp₀0 hp₀
    have hp₀1 : p₀ < 1 := lt_trans hp₀ hps1
    -- the local analytic solution of the contact system through `(ua p₀, ub p₀)`
    obtain ⟨va, vb, hva0, hvb0, hev, hana, hanb⟩ :=
      contacts_analytic hd ha0 (lt_trans has hbs) hb1 hp₀0 hp₀1 hcf0
        (slopeEq p₀ hp₀0 hp₀) (ne_of_gt hha0) (ne_of_gt hhb0)
    have hvac : ContinuousAt va p₀ := hana.continuousAt
    have hvbc : ContinuousAt vb p₀ := hanb.continuousAt
    -- eventual constraints on the local solution near `p₀`
    have hev_p : ∀ᶠ p in 𝓝 p₀, p ∈ Set.Ioo 0 (pStar d) :=
      Filter.eventually_of_mem (Ioo_mem_nhds hp₀0 hp₀) (fun _ hp => hp)
    have hev_va : ∀ᶠ p in 𝓝 p₀, va p ∈ Set.Ioo 0 (rStar d) := by
      have hm : va p₀ ∈ Set.Ioo (0:ℝ) (rStar d) := by rw [hva0]; exact ⟨ha0, has⟩
      exact hvac (Ioo_mem_nhds hm.1 hm.2)
    have hev_vb : ∀ᶠ p in 𝓝 p₀, vb p ∈ Set.Ioo (rStar d) 1 := by
      have hm : vb p₀ ∈ Set.Ioo (rStar d) (1:ℝ) := by rw [hvb0]; exact ⟨hbs, hb1⟩
      exact hvbc (Ioo_mem_nhds hm.1 hm.2)
    have hev_hva : ∀ᶠ p in 𝓝 p₀, 0 < hpd p d (va p) := by
      have hc := hpd_comp_continuousAt (d := d) hvac hp₀0 hp₀1 (by rw [hva0]; exact ha0)
        (by rw [hva0]; exact lt_trans has (rStar_lt_one hd))
      exact hc (Ioi_mem_nhds (by show (0:ℝ) < hpd p₀ d (va p₀); rw [hva0]; exact hha0))
    have hev_hvb : ∀ᶠ p in 𝓝 p₀, 0 < hpd p d (vb p) := by
      have hc := hpd_comp_continuousAt (d := d) hvbc hp₀0 hp₀1 (by rw [hvb0]; exact lt_trans hus0 hbs)
        (by rw [hvb0]; exact hb1)
      exact hc (Ioi_mem_nhds (by show (0:ℝ) < hpd p₀ d (vb p₀); rw [hvb0]; exact hhb0))
    -- on that neighbourhood both solutions are constrained, hence equal (`contact_unique`)
    have heq2 : ∀ᶠ p in 𝓝 p₀, ua p = va p ∧ ub p = vb p := by
      filter_upwards [hev, hev_p, hev_va, hev_vb, hev_hva, hev_hvb]
        with p hcfp hpp hvap hvbp hhvap hhvbp
      obtain ⟨hua0', huas', hubs', hub1', huacf', huha', huhb', _, _⟩ := spec p hpp.1 hpp.2
      have h := contact_unique hd hpp.1 hpp.2
        hvap.1 hvap.2 hvbp.1 hvbp.2 hcfp hhvap hhvbp
        hua0' huas' hubs' hub1' huacf' huha' huhb'
      exact ⟨h.1.symm, h.2.symm⟩
    exact ⟨hana.congr (heq2.mono (fun _ h => h.1.symm)),
           hanb.congr (heq2.mono (fun _ h => h.2.symm))⟩
  -- monotonicity from analyticity + the contact derivatives
  have hcontuaOn : ContinuousOn ua (Set.Ioo 0 (pStar d)) := fun p hp =>
    (hanalytic p hp.1 hp.2).1.continuousAt.continuousWithinAt
  have hcontubOn : ContinuousOn ub (Set.Ioo 0 (pStar d)) := fun p hp =>
    (hanalytic p hp.1 hp.2).2.continuousAt.continuousWithinAt
  have hsol : ∀ p, 0 < p → p < pStar d → ∀ᶠ q in 𝓝 p, contactF d (ua q, ub q) q = (0, 0) :=
    fun p hp0 hp => by
      filter_upwards [Ioo_mem_nhds hp0 hp] with q hq
      exact (spec q hq.1 hq.2).2.2.2.2.1
  -- pointwise contact-speed signs (`dx_a/dp > 0`, `dx_b/dp < 0`)
  have hderua : ∀ p, 0 < p → p < pStar d → 0 < deriv ua p := by
    intro p hp0 hp
    obtain ⟨h1, h2, h3, h4, _, h6, h7, _, _⟩ := spec p hp0 hp
    exact contact_deriv_ua_pos hd h1 (lt_trans h2 h3) h4 hp0 (lt_trans hp hps1)
      (hanalytic p hp0 hp).1.differentiableAt (hanalytic p hp0 hp).2.differentiableAt
      rfl rfl (hsol p hp0 hp) (slopeEq p hp0 hp) h6 h7
  have hderub : ∀ p, 0 < p → p < pStar d → deriv ub p < 0 := by
    intro p hp0 hp
    obtain ⟨h1, h2, h3, h4, _, h6, h7, _, _⟩ := spec p hp0 hp
    exact contact_deriv_ub_neg hd h1 (lt_trans h2 h3) h4 hp0 (lt_trans hp hps1)
      (hanalytic p hp0 hp).1.differentiableAt (hanalytic p hp0 hp).2.differentiableAt
      rfl rfl (hsol p hp0 hp) (slopeEq p hp0 hp) h6 h7
  have hmono_ua : StrictMonoOn ua (Set.Ioo 0 (pStar d)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 (pStar d)) hcontuaOn
    intro p hp; rw [interior_Ioo] at hp; exact hderua p hp.1 hp.2
  have hmono_ub : StrictAntiOn ub (Set.Ioo 0 (pStar d)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (pStar d)) hcontubOn
    intro p hp; rw [interior_Ioo] at hp; exact hderub p hp.1 hp.2
  -- the seven-conjunct `contact` field (first seven of `spec`)
  have hcontact : ∀ p, 0 < p → p < pStar d →
      0 < ua p ∧ ua p < rStar d ∧ rStar d < ub p ∧ ub p < 1 ∧
        contactF d (ua p, ub p) p = 0 ∧ 0 < hpd p d (ua p) ∧ 0 < hpd p d (ub p) := by
    intro p hp0 hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, _, _⟩ := spec p hp0 hp
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hsupua : ∀ p, 0 < p → p < pStar d → ∀ x ∈ Set.Icc (0:ℝ) 1,
      phi p d ((ua p) ^ d) + deriv (phi p d) ((ua p) ^ d) * (x - (ua p) ^ d) ≤ phi p d x :=
    fun p hp0 hp => (spec p hp0 hp).2.2.2.2.2.2.2.1
  have hsupub : ∀ p, 0 < p → p < pStar d → ∀ x ∈ Set.Icc (0:ℝ) 1,
      phi p d ((ub p) ^ d) + deriv (phi p d) ((ub p) ^ d) * (x - (ub p) ^ d) ≤ phi p d x :=
    fun p hp0 hp => (spec p hp0 hp).2.2.2.2.2.2.2.2
  have G : GlobalContacts d :=
    { ua := ua, ub := ub, contact := hcontact,
      analytic_ua := fun p hp0 hp => (hanalytic p hp0 hp).1,
      analytic_ub := fun p hp0 hp => (hanalytic p hp0 hp).2,
      mono_ua := hmono_ua, mono_ub := hmono_ub,
      deriv_ua_pos := hderua, deriv_ub_neg := hderub,
      support_ua := hsupua, support_ub := hsupub,
      ua_lim_pStar := lim1, ub_lim_pStar := lim2, ua_lim_zero := lim3, ub_lim_zero := lim4 }
  exact ⟨G⟩

/-- **Construction data for an oriented regular Lubetzky–Zhao boundary arc through `r₀`.**  Bundles
the interval `U ∋ r₀` (with `r ≠ r_*` throughout), the analytic boundary curve `pc`
and second-contact map `sm`, the three shallow `LZBoundaryArc` fields `ordering`,
`supporting`, `secondContact`, and — for the regularity fields `quadSep`, `orientation`,
`noFlatTie` — the underlying `GlobalContacts` together with
the family link identifying `(r, sm r)` with the contacts at parameter `pc r`. -/
structure ArcMaps (d : ℕ) (r₀ : ℝ) where
  /-- The parameter interval. -/
  U : Set ℝ
  isOpen_U : IsOpen U
  /-- `r₀` is in the interval. -/
  mem : r₀ ∈ U
  /-- Every density in the interval is non-exceptional. -/
  notExc : ∀ r ∈ U, r ≠ rStar d
  /-- The Lubetzky–Zhao boundary curve `p = pc(r)`. -/
  pc : ℝ → ℝ
  /-- The second-contact density `s(r)`. -/
  sm : ℝ → ℝ
  analytic_pc : AnalyticOnNhd ℝ pc U
  analytic_sm : AnalyticOnNhd ℝ sm U
  /-- The `LZBoundaryArc.ordering` field (part of (M1) of `thm:scalar-lz-boundary`). -/
  ordering : ∀ r ∈ U, 0 < pc r ∧ pc r < r ∧ r < 1 ∧ sm r ≠ r ∧ 0 < sm r ∧ sm r < 1
  /-- The `LZBoundaryArc.supporting` field ((M3) of `thm:scalar-lz-boundary`): the tangent line at
  `r^d` lies below the graph. -/
  supporting : ∀ r ∈ U, ∀ u ∈ Set.Icc (0:ℝ) 1,
    Jp (pc r) r + slope d pc r * (u ^ d - r ^ d) ≤ Jp (pc r) u
  /-- The `LZBoundaryArc.secondContact` field (half of (M4) of `thm:scalar-lz-boundary`): a second
  contact at `sm(r)^d`. -/
  secondContact : ∀ r ∈ U,
    Jp (pc r) (sm r) = Jp (pc r) r + slope d pc r * ((sm r) ^ d - r ^ d)
  /-- The global contact data underlying this arc. -/
  gc : GlobalContacts d
  /-- Family link: `pc r ∈ (0,p_*)` is the parameter whose Lubetzky–Zhao contact at the
  target is `r`, with `sm r` the other contact.  Lower family `r < r_*`: `r = u_a(pc r)`,
  `sm r = u_b(pc r)`; upper family `r > r_*`: `r = u_b(pc r)`, `sm r = u_a(pc r)`. -/
  family : ∀ r ∈ U, pc r ∈ Set.Ioo (0:ℝ) (pStar d) ∧
    ((r < rStar d ∧ gc.ua (pc r) = r ∧ sm r = gc.ub (pc r)) ∨
     (rStar d < r ∧ gc.ub (pc r) = r ∧ sm r = gc.ua (pc r)))

/-- `J_p(u) = φ_{p,d}(u^d)` for `u ≥ 0` (the `x = u^d` form of `phi_pow_eq_Jp`,
extended to `u = 0`). -/
theorem Jp_eq_phi_pow {p : ℝ} {d : ℕ} (hd : 2 ≤ d) {u : ℝ} (hu : 0 ≤ u) :
    Jp p u = phi p d (u ^ d) := by
  have hd0 : d ≠ 0 := by omega
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hne : (1:ℝ) / (d:ℝ) ≠ 0 := by positivity
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h, zero_pow hd0, phi_eq_Jp_rpow,
      show Real.rpow 0 (1/(d:ℝ)) = 0 from Real.zero_rpow hne]
  · exact (phi_pow_eq_Jp hd h).symm

/-- The supporting-line slope coincides with the contact slope `deriv φ` at `r^d`. -/
theorem slope_eq_deriv_phi {d : ℕ} (hd : 2 ≤ d) {pc : ℝ → ℝ} {r : ℝ}
    (hp0 : 0 < pc r) (hp1 : pc r < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    slope d pc r = deriv (phi (pc r) d) (r ^ d) := by
  rw [deriv_phi_pow_eq_sCM hd hp0 hp1 hr0 hr1]
  simp only [slope, sCM]

/-- `J_p'(p) = 0`: the relative entropy slope vanishes at the background density. -/
theorem Jp'_self_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : Jp' p p = 0 := by
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1pne : (1:ℝ) - p ≠ 0 := ne_of_gt (by linarith)
  unfold Jp'
  rw [show p * (1 - p) / ((1 - p) * p) = 1 by field_simp, Real.log_one]

open Filter Topology in
/-- **Generic analytic-inverse patch.**  If `f` is analytic with non-vanishing
derivative and injective on `(0,p_*)`, and `pc` is a right inverse of `f` over an open
set `U` (taking values in `(0,p_*)`), then `pc` is analytic on `U`. -/
theorem analyticOn_inverse_family {d : ℕ} {f pc : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U)
    (hf_an : ∀ p ∈ Set.Ioo (0:ℝ) (pStar d), AnalyticAt ℝ f p)
    (hf_deriv : ∀ p ∈ Set.Ioo (0:ℝ) (pStar d), deriv f p ≠ 0)
    (hf_inj : Set.InjOn f (Set.Ioo (0:ℝ) (pStar d)))
    (hpc : ∀ r ∈ U, pc r ∈ Set.Ioo (0:ℝ) (pStar d) ∧ f (pc r) = r) :
    ∀ r ∈ U, AnalyticAt ℝ pc r := by
  intro r₁ hr₁
  obtain ⟨hp₁mem, hf_p₁⟩ := hpc r₁ hr₁
  set p₁ := pc r₁ with hp₁
  have hfa : AnalyticAt ℝ f p₁ := hf_an p₁ hp₁mem
  have hfa' : deriv f p₁ ≠ 0 := hf_deriv p₁ hp₁mem
  obtain ⟨g, hg_an, hg_eq, _, hg_right⟩ := contact_localInverse_analytic hfa hfa'
  rw [hf_p₁] at hg_an hg_eq hg_right
  have hg_cont : ContinuousAt g r₁ := hg_an.continuousAt
  have hg_mem : ∀ᶠ s in 𝓝 r₁, g s ∈ Set.Ioo (0:ℝ) (pStar d) := by
    have hmem : g r₁ ∈ Set.Ioo (0:ℝ) (pStar d) := by rw [hg_eq]; exact hp₁mem
    exact hg_cont (Ioo_mem_nhds hmem.1 hmem.2)
  have hU_mem : ∀ᶠ s in 𝓝 r₁, s ∈ U :=
    Filter.eventually_of_mem (hU.mem_nhds hr₁) (fun s hs => hs)
  have hcong : pc =ᶠ[𝓝 r₁] g := by
    filter_upwards [hg_mem, hg_right, hU_mem] with s hsg hsr hsU
    obtain ⟨hpc_mem, hpc_f⟩ := hpc s hsU
    exact hf_inj hpc_mem hsg (hpc_f.trans hsr.symm)
  exact hg_an.congr hcong.symm

/-! ## Lower family `r₀ < r_*` -/

theorem arcMaps_lower {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {r₀ : ℝ}
    (hr₀0 : 0 < r₀) (hlow : r₀ < rStar d) : Nonempty (ArcMaps d r₀) := by
  classical
  have hps0 : 0 < pStar d := pStar_pos hd
  have hps1 : pStar d < 1 := pStar_lt_one hd
  have hus0 : 0 < rStar d := rStar_pos hd
  have hus1 : rStar d < 1 := rStar_lt_one hd
  have hpsus : pStar d < rStar d := pStar_lt_rStar hd
  set U : Set ℝ := Set.Ioo (0:ℝ) (rStar d) with hUdef
  have hUopen : IsOpen U := isOpen_Ioo
  have hr₀U : r₀ ∈ U := ⟨hr₀0, hlow⟩
  have hex : ∀ r ∈ U, ∃ p, p ∈ Set.Ioo (0:ℝ) (pStar d) ∧ G.ua p = r := by
    intro r hr; obtain ⟨p, hp, hpe⟩ := G.surjOn_ua hd hr; exact ⟨p, hp, hpe⟩
  -- the boundary curve and second-contact map
  let pc : ℝ → ℝ := fun r => if h : r ∈ U then (hex r h).choose else 0
  let sm : ℝ → ℝ := fun r => G.ub (pc r)
  have hpc_spec : ∀ r ∈ U, pc r ∈ Set.Ioo (0:ℝ) (pStar d) ∧ G.ua (pc r) = r := by
    intro r hr
    have he : pc r = (hex r hr).choose := dif_pos hr
    rw [he]; exact (hex r hr).choose_spec
  -- M1's `pc r < r`
  have hpc_lt : ∀ r ∈ U, pc r < r := by
    intro r hr
    obtain ⟨hpc_io, hpc_ua⟩ := hpc_spec r hr
    set p := pc r with hp
    have hp0 : 0 < p := hpc_io.1
    have hpps : p < pStar d := hpc_io.2
    have hp1 : p < 1 := lt_trans hpps hps1
    obtain ⟨hua0, huas, hubs, hub1, hcf, _, _⟩ := G.contact p hp0 hpps
    have hua1 : G.ua p < 1 := lt_trans huas hus1
    have hub0 : 0 < G.ub p := lt_trans hus0 hubs
    have hsupp := G.support_ua p hp0 hpps
    have hsnd : Jp p (G.ub p) - Jp p (G.ua p)
        - sCM d p (G.ua p) * ((G.ub p) ^ d - (G.ua p) ^ d) = 0 := by
      have hx := (Prod.ext_iff.mp hcf).2
      simpa only [contactF, Prod.snd_zero] using hx
    set m := deriv (phi p d) ((G.ua p) ^ d) with hm
    have hpp01 : p ^ d ∈ Set.Icc (0:ℝ) 1 := ⟨pow_nonneg hp0.le d, pow_le_one₀ hp0.le hp1.le⟩
    have hphipp : phi p d (p ^ d) = 0 := by rw [phi_pow_eq_Jp hd hp0, Jp_self hp0 hp1]
    have hI : phi p d ((G.ua p) ^ d) + m * (p ^ d - (G.ua p) ^ d) ≤ 0 := by
      have h := hsupp (p ^ d) hpp01; rw [hphipp] at h; exact h
    have hma : m = sCM d p (G.ua p) :=
      hm.trans (deriv_phi_pow_eq_sCM hd hp0 hp1 hua0 hua1)
    have hchord : phi p d ((G.ub p) ^ d)
        = phi p d ((G.ua p) ^ d) + m * ((G.ub p) ^ d - (G.ua p) ^ d) := by
      rw [phi_pow_eq_Jp hd hub0, phi_pow_eq_Jp hd hua0, hma]; linarith [hsnd]
    have hphib_pos : 0 < phi p d ((G.ub p) ^ d) := by
      rw [phi_pow_eq_Jp hd hub0]
      exact Jp_pos_of_gt hp0 hp1 (lt_trans hpps (lt_trans hpsus hubs)) hub1
    have hpp_lt_b : p ^ d < (G.ub p) ^ d :=
      pow_lt_pow_left₀ (lt_trans hpps (lt_trans hpsus hubs)) hp0.le (by omega)
    have h2 : 0 < phi p d ((G.ua p) ^ d) + m * ((G.ub p) ^ d - (G.ua p) ^ d) := by
      rw [← hchord]; exact hphib_pos
    have h3 : m * (p ^ d - (G.ub p) ^ d) < 0 := by nlinarith [hI, h2]
    have hm_pos : 0 < m := by nlinarith [h3, hpp_lt_b]
    have hJp'pos : 0 < Jp' p (G.ua p) := by
      have hsCMpos : 0 < sCM d p (G.ua p) := hma ▸ hm_pos
      have hden : 0 < (d:ℝ) * (G.ua p) ^ (d - 1) := by
        have : (0:ℝ) < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
        positivity
      rw [sCM, lt_div_iff₀ hden, zero_mul] at hsCMpos
      exact hsCMpos
    have hua_gt : p < G.ua p := by
      by_contra hle; push Not at hle
      rcases hle.lt_or_eq with hlt | heq
      · linarith [Jp'_neg_of_lt hua0 hlt hp1, hJp'pos]
      · rw [heq, Jp'_self_zero hp0 hp1] at hJp'pos; exact lt_irrefl 0 hJp'pos
    rw [hpc_ua] at hua_gt; exact hua_gt
  -- analyticity of `pc`
  have hpc_an : ∀ r ∈ U, AnalyticAt ℝ pc r :=
    analyticOn_inverse_family hUopen
      (fun p hp => G.analytic_ua p hp.1 hp.2)
      (fun p hp => ne_of_gt (G.deriv_ua_pos p hp.1 hp.2))
      G.injOn_ua hpc_spec
  have hsm_an : ∀ r ∈ U, AnalyticAt ℝ sm r := by
    intro r hr
    obtain ⟨hpc_io, _⟩ := hpc_spec r hr
    exact (G.analytic_ub (pc r) hpc_io.1 hpc_io.2).comp (hpc_an r hr)
  -- M2 supporting line
  have hM2 : ∀ r ∈ U, ∀ u ∈ Set.Icc (0:ℝ) 1,
      Jp (pc r) r + slope d pc r * (u ^ d - r ^ d) ≤ Jp (pc r) u := by
    intro r hr u hu
    obtain ⟨hpc_io, hpc_ua⟩ := hpc_spec r hr
    have hp0 : 0 < pc r := hpc_io.1
    have hpps : pc r < pStar d := hpc_io.2
    have hp1 : pc r < 1 := lt_trans hpps hps1
    obtain ⟨hua0, huas, _, _, _, _, _⟩ := G.contact (pc r) hp0 hpps
    have hr0 : 0 < r := hpc_ua ▸ hua0
    have hr1 : r < 1 := hpc_ua ▸ (lt_trans huas hus1)
    have hsupp := G.support_ua (pc r) hp0 hpps
    rw [hpc_ua] at hsupp
    have hud01 : u ^ d ∈ Set.Icc (0:ℝ) 1 := ⟨pow_nonneg hu.1 d, pow_le_one₀ hu.1 hu.2⟩
    have key := hsupp (u ^ d) hud01
    have hsl : slope d pc r = deriv (phi (pc r) d) (r ^ d) :=
      slope_eq_deriv_phi hd hp0 hp1 hr0 hr1
    rw [Jp_eq_phi_pow hd hr0.le, hsl, Jp_eq_phi_pow hd hu.1]
    exact key
  -- M3 second contact
  have hM3 : ∀ r ∈ U,
      Jp (pc r) (sm r) = Jp (pc r) r + slope d pc r * ((sm r) ^ d - r ^ d) := by
    intro r hr
    obtain ⟨hpc_io, hpc_ua⟩ := hpc_spec r hr
    have hp0 : 0 < pc r := hpc_io.1
    have hpps : pc r < pStar d := hpc_io.2
    obtain ⟨_, _, _, _, hcf, _, _⟩ := G.contact (pc r) hp0 hpps
    have hsnd : Jp (pc r) (G.ub (pc r)) - Jp (pc r) (G.ua (pc r))
        - sCM d (pc r) (G.ua (pc r)) * ((G.ub (pc r)) ^ d - (G.ua (pc r)) ^ d) = 0 := by
      have hx := (Prod.ext_iff.mp hcf).2
      simpa only [contactF, Prod.snd_zero] using hx
    have hsm : sm r = G.ub (pc r) := rfl
    have hslr : slope d pc r = sCM d (pc r) r := rfl
    rw [hpc_ua] at hsnd
    rw [hsm, hslr]; linarith [hsnd]
  -- the `ordering` field
  have hord : ∀ r ∈ U, 0 < pc r ∧ pc r < r ∧ r < 1 ∧ sm r ≠ r ∧ 0 < sm r ∧ sm r < 1 := by
    intro r hr
    obtain ⟨hpc_io, _⟩ := hpc_spec r hr
    obtain ⟨_, _, hubs, hub1, _, _, _⟩ := G.contact (pc r) hpc_io.1 hpc_io.2
    have hsm_eq : sm r = G.ub (pc r) := rfl
    have hsm_gt : rStar d < sm r := by rw [hsm_eq]; exact hubs
    refine ⟨hpc_io.1, hpc_lt r hr, lt_trans hr.2 hus1,
      ne_of_gt (lt_trans hr.2 hsm_gt), lt_trans hus0 hsm_gt, ?_⟩
    rw [hsm_eq]; exact hub1
  -- assemble
  have A : ArcMaps d r₀ :=
    { U := U, isOpen_U := hUopen, mem := hr₀U,
      notExc := fun r hr => ne_of_lt hr.2,
      pc := pc, sm := sm, analytic_pc := hpc_an, analytic_sm := hsm_an,
      ordering := hord, supporting := hM2, secondContact := hM3,
      gc := G,
      family := fun r hr => ⟨(hpc_spec r hr).1, Or.inl ⟨hr.2, (hpc_spec r hr).2, rfl⟩⟩ }
  exact ⟨A⟩

/-! ## Upper family `r_* < r₀` -/

theorem arcMaps_upper {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {r₀ : ℝ}
    (hupp : rStar d < r₀) (hr₀1 : r₀ < 1) : Nonempty (ArcMaps d r₀) := by
  classical
  have hps0 : 0 < pStar d := pStar_pos hd
  have hps1 : pStar d < 1 := pStar_lt_one hd
  have hus0 : 0 < rStar d := rStar_pos hd
  have hus1 : rStar d < 1 := rStar_lt_one hd
  have hpsus : pStar d < rStar d := pStar_lt_rStar hd
  set U : Set ℝ := Set.Ioo (rStar d) 1 with hUdef
  have hUopen : IsOpen U := isOpen_Ioo
  have hr₀U : r₀ ∈ U := ⟨hupp, hr₀1⟩
  have hex : ∀ r ∈ U, ∃ p, p ∈ Set.Ioo (0:ℝ) (pStar d) ∧ G.ub p = r := by
    intro r hr; obtain ⟨p, hp, hpe⟩ := G.surjOn_ub hd hr; exact ⟨p, hp, hpe⟩
  let pc : ℝ → ℝ := fun r => if h : r ∈ U then (hex r h).choose else 0
  let sm : ℝ → ℝ := fun r => G.ua (pc r)
  have hpc_spec : ∀ r ∈ U, pc r ∈ Set.Ioo (0:ℝ) (pStar d) ∧ G.ub (pc r) = r := by
    intro r hr
    have he : pc r = (hex r hr).choose := dif_pos hr
    rw [he]; exact (hex r hr).choose_spec
  -- analyticity of `pc`
  have hpc_an : ∀ r ∈ U, AnalyticAt ℝ pc r :=
    analyticOn_inverse_family hUopen
      (fun p hp => G.analytic_ub p hp.1 hp.2)
      (fun p hp => ne_of_lt (G.deriv_ub_neg p hp.1 hp.2))
      G.injOn_ub hpc_spec
  have hsm_an : ∀ r ∈ U, AnalyticAt ℝ sm r := by
    intro r hr
    obtain ⟨hpc_io, _⟩ := hpc_spec r hr
    exact (G.analytic_ua (pc r) hpc_io.1 hpc_io.2).comp (hpc_an r hr)
  -- M2 supporting line
  have hM2 : ∀ r ∈ U, ∀ u ∈ Set.Icc (0:ℝ) 1,
      Jp (pc r) r + slope d pc r * (u ^ d - r ^ d) ≤ Jp (pc r) u := by
    intro r hr u hu
    obtain ⟨hpc_io, hpc_ub⟩ := hpc_spec r hr
    have hp0 : 0 < pc r := hpc_io.1
    have hpps : pc r < pStar d := hpc_io.2
    have hp1 : pc r < 1 := lt_trans hpps hps1
    obtain ⟨_, _, hubs, hub1, _, _, _⟩ := G.contact (pc r) hp0 hpps
    have hr0 : 0 < r := hpc_ub ▸ (lt_trans hus0 hubs)
    have hr1 : r < 1 := hpc_ub ▸ hub1
    have hsupp := G.support_ub (pc r) hp0 hpps
    rw [hpc_ub] at hsupp
    have hud01 : u ^ d ∈ Set.Icc (0:ℝ) 1 := ⟨pow_nonneg hu.1 d, pow_le_one₀ hu.1 hu.2⟩
    have key := hsupp (u ^ d) hud01
    have hsl : slope d pc r = deriv (phi (pc r) d) (r ^ d) :=
      slope_eq_deriv_phi hd hp0 hp1 hr0 hr1
    rw [Jp_eq_phi_pow hd hr0.le, hsl, Jp_eq_phi_pow hd hu.1]
    exact key
  -- M3 second contact
  have hM3 : ∀ r ∈ U,
      Jp (pc r) (sm r) = Jp (pc r) r + slope d pc r * ((sm r) ^ d - r ^ d) := by
    intro r hr
    obtain ⟨hpc_io, hpc_ub⟩ := hpc_spec r hr
    have hp0 : 0 < pc r := hpc_io.1
    have hpps : pc r < pStar d := hpc_io.2
    obtain ⟨_, _, _, _, hcf, _, _⟩ := G.contact (pc r) hp0 hpps
    have hsnd : Jp (pc r) (G.ub (pc r)) - Jp (pc r) (G.ua (pc r))
        - sCM d (pc r) (G.ua (pc r)) * ((G.ub (pc r)) ^ d - (G.ua (pc r)) ^ d) = 0 := by
      have hx := (Prod.ext_iff.mp hcf).2
      simpa only [contactF, Prod.snd_zero] using hx
    have hfst : sCM d (pc r) (G.ua (pc r)) - sCM d (pc r) (G.ub (pc r)) = 0 := by
      have hx := (Prod.ext_iff.mp hcf).1
      simpa only [contactF, Prod.fst_zero] using hx
    have hsm : sm r = G.ua (pc r) := rfl
    have hslr : slope d pc r = sCM d (pc r) r := rfl
    rw [hpc_ub] at hsnd hfst
    have hsCM_eq : sCM d (pc r) (G.ua (pc r)) = sCM d (pc r) r := by linarith [hfst]
    rw [hsm, hslr, ← hsCM_eq]
    linear_combination -hsnd
  -- the `ordering` field
  have hord : ∀ r ∈ U, 0 < pc r ∧ pc r < r ∧ r < 1 ∧ sm r ≠ r ∧ 0 < sm r ∧ sm r < 1 := by
    intro r hr
    obtain ⟨hpc_io, _⟩ := hpc_spec r hr
    obtain ⟨hua0, huas, _, _, _, _, _⟩ := G.contact (pc r) hpc_io.1 hpc_io.2
    have hsm_eq : sm r = G.ua (pc r) := rfl
    have hsm_lt : sm r < rStar d := by rw [hsm_eq]; exact huas
    refine ⟨hpc_io.1, lt_trans hpc_io.2 (lt_trans hpsus hr.1), hr.2,
      ne_of_lt (lt_trans hsm_lt hr.1), ?_, ?_⟩
    · rw [hsm_eq]; exact hua0
    · rw [hsm_eq]; exact lt_trans huas hus1
  -- assemble
  have A : ArcMaps d r₀ :=
    { U := U, isOpen_U := hUopen, mem := hr₀U,
      notExc := fun r hr => ne_of_gt hr.1,
      pc := pc, sm := sm, analytic_pc := hpc_an, analytic_sm := hsm_an,
      ordering := hord, supporting := hM2, secondContact := hM3,
      gc := G,
      family := fun r hr => ⟨(hpc_spec r hr).1, Or.inr ⟨hr.1, (hpc_spec r hr).2, rfl⟩⟩ }
  exact ⟨A⟩

/-- **Construction of the arc from the global contacts** (inversion half of
`thm:scalar-lz-boundary`).  Given the global Lubetzky–Zhao contact maps, invert the relevant family (`u_a` if
`r₀ < r_*`, `u_b` if `r₀ > r_*`) to the analytic boundary curve `pc` on an interval
`U ∋ r₀` (analytic inverse function theorem `contact_localInverse_analytic` patched
over `U`, the bijection from `mono_ua`/`mono_ub` + the endpoint limits via
`ContinuousOn.surjOn_of_tendsto`), set `sm` from the other family, and read off
the three shallow fields: `ordering`'s `pc(r) < r` uses `pStar_lt_rStar` and the
convex-minorant value at `p^d`; `secondContact` is the chord equation transported by
`phi_eq_Jp_rpow`/`deriv_phi_eq_sCM`; `supporting` is the supporting line.  Carries the
`GlobalContacts` and family link through. -/
theorem arcMaps_of_globalContacts {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {r₀ : ℝ}
    (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1) (hexc : r₀ ≠ rStar d) :
    Nonempty (ArcMaps d r₀) := by
  rcases lt_or_gt_of_ne hexc with hlow | hupp
  · exact arcMaps_lower hd G hr₀0 hlow
  · exact arcMaps_upper hd G hupp hr₀1

/-- **Construction half of `thm:scalar-lz-boundary`** (the three shallow fields), now factored
through the keystone
`GlobalContacts`: the global contact maps exist (`exists_globalContacts`) and the arc
is built by inverting the relevant family (`arcMaps_of_globalContacts`). -/
theorem exists_arcMaps {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ}
    (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1) (hexc : r₀ ≠ rStar d) :
    Nonempty (ArcMaps d r₀) := by
  obtain ⟨G⟩ := exists_globalContacts hd
  exact arcMaps_of_globalContacts hd G hr₀0 hr₀1 hexc

/-! ### Shared convex-minorant lemmas for the regularity conditions (M4–M6) -/

/-- A convex function on `[a,b]` has a supporting line at every interior point:
`g c + m (t - c) ≤ g t` with `m` the right derivative.  (Extracted from the
`lce_largest` argument.) -/
theorem convexOn_supporting_line {a b : ℝ} {g : ℝ → ℝ}
    (hgc : ConvexOn ℝ (Set.Icc a b) g) {c : ℝ} (hc : c ∈ Set.Ioo a b) :
    ∃ m : ℝ, ∀ t ∈ Set.Icc a b, m * t + (g c - m * c) ≤ g t := by
  have hcI : c ∈ interior (Set.Icc a b) := by rw [interior_Icc]; exact hc
  set m := derivWithin g (Set.Ioi c) c with hm
  refine ⟨m, fun t ht => ?_⟩
  rcases lt_trichotomy t c with htx | htx | htx
  · have h1 := hgc.slope_le_leftDeriv_of_mem_interior ht hcI htx
    have h2 := hgc.leftDeriv_le_rightDeriv_of_mem_interior hcI
    rw [← hm] at h2
    have hsl : _root_.slope g t c ≤ m := le_trans h1 h2
    rw [_root_.slope_def_field] at hsl
    have hxt : 0 < c - t := by linarith
    have hkey := (div_le_iff₀ hxt).mp hsl
    linarith [hkey, mul_sub m c t]
  · subst htx; linarith
  · have h1 := hgc.rightDeriv_le_slope_of_mem_interior hcI ht htx
    rw [← hm] at h1
    rw [_root_.slope_def_field] at h1
    have hxt : 0 < t - c := by linarith
    have hkey := (le_div_iff₀ hxt).mp h1
    linarith [hkey, mul_sub m t c]

/-- **Supporting line ⟺ on the convex minorant.**  For continuous `f` on `[a,b]` and an
interior point `c`, a supporting line of `f` through `(c, f c)` exists iff the convex
minorant agrees with `f` at `c`.  This is the bridge the `orientation` field uses: no supporting
line at `r^d` ⟺ `lce < φ` there. -/
theorem exists_supportingLine_iff_lce_eq {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {c : ℝ} (hc : c ∈ Set.Ioo a b) :
    (∃ s : ℝ, ∀ x ∈ Set.Icc a b, f c + s * (x - c) ≤ f x) ↔ lce a b f c = f c := by
  have hcIcc : c ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hc
  constructor
  · rintro ⟨s, hs⟩
    have hmin : ∀ t ∈ Set.Icc a b, s * t + (f c - s * c) ≤ f t := by
      intro t ht; have := hs t ht; nlinarith [this]
    have hle : f c ≤ lce a b f c := by
      have h := affine_le_lce hmin hcIcc
      have he : s * c + (f c - s * c) = f c := by ring
      linarith [he ▸ h]
    exact le_antisymm (lce_le_self hab.le hf hcIcc) hle
  · intro hlce
    obtain ⟨m, hm⟩ := convexOn_supporting_line (convexOn_lce hab.le hf) hc
    refine ⟨m, fun x hx => ?_⟩
    have h1 : m * x + (lce a b f c - m * c) ≤ lce a b f x := hm x hx
    have h2 : lce a b f x ≤ f x := lce_le_self hab.le hf hx
    rw [hlce] at h1
    nlinarith [h1, h2]

/-- **Convex-minorant position at the Lubetzky–Zhao contacts.**  For `p ∈ (0,p_*)`, the convex
minorant `lce` of `φ_{p,d}` agrees with `φ_{p,d}` at the two contacts `(u_a(p))^d`,
`(u_b(p))^d` and is *strictly* below `φ_{p,d}` strictly between them.  Identifies the
detached affine component of `exists_lz_boundary_component` with the `GlobalContacts`
contacts via per-`p` uniqueness (`contact_unique`).  This decides, in `orientation` and
`noFlatTie`,
whether `r^d` admits a supporting line: yes iff `r^d ∉ ((u_a p)^d, (u_b p)^d)`. -/
theorem gc_lce_at_contacts {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {p : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) :
    lce 0 1 (phi p d) ((G.ua p) ^ d) = phi p d ((G.ua p) ^ d) ∧
    lce 0 1 (phi p d) ((G.ub p) ^ d) = phi p d ((G.ub p) ^ d) ∧
    (∀ x ∈ Set.Ioo ((G.ua p) ^ d) ((G.ub p) ^ d), lce 0 1 (phi p d) x < phi p d x) := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  obtain ⟨xa, xb, hxa0, hab, hxb1, hslope, hchord, hxaStar, hStarXb, hhpa, hhpb,
      _, _, hLxa, hLxb, hLlt⟩ := lz_boundary_contacts hd hp0 hp
  have hzpos : (0:ℝ) < 1 / (d:ℝ) := by have := dpos hd; positivity
  have hStarEq : Real.rpow ((rStar d) ^ d) (1/(d:ℝ)) = rStar d := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast (rStar_pos hd).le (by omega)
  have hpow_a : (Real.rpow xa (1/(d:ℝ))) ^ d = xa := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hxa0.le (by omega)
  have hpow_b : (Real.rpow xb (1/(d:ℝ))) ^ d = xb := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow (lt_trans hxa0 hab).le (by omega)
  have ha0 : 0 < Real.rpow xa (1/(d:ℝ)) := Real.rpow_pos_of_pos hxa0 _
  have has : Real.rpow xa (1/(d:ℝ)) < rStar d := by
    rw [← hStarEq]; exact Real.rpow_lt_rpow hxa0.le hxaStar hzpos
  have hbs : rStar d < Real.rpow xb (1/(d:ℝ)) := by
    rw [← hStarEq]; exact Real.rpow_lt_rpow (pow_nonneg (rStar_pos hd).le d) hStarXb hzpos
  have hb1 : Real.rpow xb (1/(d:ℝ)) < 1 := by
    have h : Real.rpow xb (1/(d:ℝ)) < Real.rpow 1 (1/(d:ℝ)) :=
      Real.rpow_lt_rpow (lt_trans hxa0 hab).le hxb1 hzpos
    simpa using h
  have hcf : contactF d (Real.rpow xa (1/(d:ℝ)), Real.rpow xb (1/(d:ℝ))) p = 0 :=
    contactF_of_phi_contacts hd hp0 hp1 hxa0 hab hxb1 hslope hchord
  obtain ⟨hua0, huas, hubs, hub1, hcfG, hhuaG, hhubG⟩ := G.contact p hp0 hp
  obtain ⟨heqa, heqb⟩ := contact_unique hd hp0 hp ha0 has hbs hb1 hcf hhpa hhpb
    hua0 huas hubs hub1 hcfG hhuaG hhubG
  have hxa_eq : xa = (G.ua p) ^ d := by rw [← hpow_a, heqa]
  have hxb_eq : xb = (G.ub p) ^ d := by rw [← hpow_b, heqb]
  rw [hxa_eq] at hLxa
  rw [hxb_eq] at hLxb
  rw [hxa_eq, hxb_eq] at hLlt
  exact ⟨hLxa, hLxb, hLlt⟩

/-- A convex function lies above its tangent line at any point of differentiability. -/
theorem convexOn_tangent_le {S : Set ℝ} {f : ℝ → ℝ} {f' x₀ : ℝ}
    (hfc : ConvexOn ℝ S f) (hx₀ : x₀ ∈ S) (hderiv : HasDerivAt f f' x₀) :
    ∀ y ∈ S, f x₀ + f' * (y - x₀) ≤ f y := by
  intro y hy
  rcases lt_trichotomy x₀ y with hlt | heq | hgt
  · have h := hfc.le_slope_of_hasDerivAt hx₀ hy hlt hderiv
    rw [_root_.slope_def_field] at h
    have hpos : 0 < y - x₀ := by linarith
    rw [le_div_iff₀ hpos] at h
    linarith
  · subst heq; simp
  · have h := hfc.slope_le_of_hasDerivAt hy hx₀ hgt hderiv
    rw [_root_.slope_def_field] at h
    have hpos : 0 < x₀ - y := by linarith
    rw [div_le_iff₀ hpos] at h
    linarith

/-- **Supporting line on the right convex piece.**  If `φ_{p,d}'' > 0` on `(c,1)` and there
is an affine minorant tangent at `c` (slope `φ'(c)`), then every `x₀ ∈ (c,1)` admits a
global supporting line of `φ_{p,d}`.  (The "outside the component ⟹ supporting line
exists" half of `orientation`/`noFlatTie` on the right.) -/
theorem supportingLine_right_of_convex {d : ℕ} {p c x₀ : ℝ}
    (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    (hc0 : 0 < c) (hcx₀ : c < x₀) (hx₀1 : x₀ < 1)
    (hconv : ∀ x ∈ Set.Ioo c 1, 0 < phi'' p d x)
    (hmin : ∀ x ∈ Set.Icc (0:ℝ) 1, phi p d c + deriv (phi p d) c * (x - c) ≤ phi p d x) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, phi p d x₀ + deriv (phi p d) x₀ * (x - x₀) ≤ phi p d x := by
  have hc1 : c < 1 := lt_trans hcx₀ hx₀1
  -- `φ` is convex on `[c,1]`
  have hcont : ContinuousOn (phi p d) (Set.Icc c 1) :=
    (phi_continuousOn_Icc hd hp0 hp1).mono (Set.Icc_subset_Icc hc0.le le_rfl)
  have hdiff : DifferentiableOn ℝ (phi p d) (interior (Set.Icc c 1)) := by
    rw [interior_Icc]; intro x hx
    exact (hasDerivAt_phi hd hp0 hp1 (lt_trans hc0 hx.1) hx.2).differentiableAt.differentiableWithinAt
  have hdiff2 : DifferentiableOn ℝ (deriv (phi p d)) (interior (Set.Icc c 1)) := by
    rw [interior_Icc]; intro x hx
    exact (hasDerivAt_phi'' hd hp0 hp1 (lt_trans hc0 hx.1) hx.2).differentiableAt.differentiableWithinAt
  have hnn : ∀ x ∈ interior (Set.Icc c 1), 0 ≤ deriv^[2] (phi p d) x := by
    rw [interior_Icc]; intro x hx
    have he : deriv^[2] (phi p d) x = phi'' p d x := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact (hasDerivAt_phi'' hd hp0 hp1 (lt_trans hc0 hx.1) hx.2).deriv
    rw [he]; exact (hconv x hx).le
  have hconvex : ConvexOn ℝ (Set.Icc c 1) (phi p d) :=
    convexOn_of_deriv2_nonneg (convex_Icc c 1) hcont hdiff hdiff2 hnn
  -- derivatives at `x₀` and `c`
  have hHx₀ : HasDerivAt (phi p d) (deriv (phi p d) x₀) x₀ := by
    have h := hasDerivAt_phi hd hp0 hp1 (lt_trans hc0 hcx₀) hx₀1; rw [h.deriv]; exact h
  have hHc : HasDerivAt (phi p d) (deriv (phi p d) c) c := by
    have h := hasDerivAt_phi hd hp0 hp1 hc0 hc1; rw [h.deriv]; exact h
  have hx₀Icc : x₀ ∈ Set.Icc c 1 := ⟨hcx₀.le, hx₀1.le⟩
  have hcIcc : c ∈ Set.Icc c 1 := ⟨le_refl c, hc1.le⟩
  set s := deriv (phi p d) x₀ with hs
  set m := deriv (phi p d) c with hmm
  -- tangent below on `[c,1]`
  have htan : ∀ y ∈ Set.Icc c 1, phi p d x₀ + s * (y - x₀) ≤ phi p d y :=
    convexOn_tangent_le hconvex hx₀Icc hHx₀
  -- `m ≤ s`
  have hms : m ≤ s := by
    have h1 := hconvex.le_slope_of_hasDerivAt hcIcc hx₀Icc hcx₀ hHc
    have h2 := hconvex.slope_le_of_hasDerivAt hcIcc hx₀Icc hcx₀ hHx₀
    exact le_trans h1 h2
  intro x hx
  rcases le_total c x with hcx | hxc
  · exact htan x ⟨hcx, hx.2⟩
  · -- `x ≤ c`: glue through the affine minorant
    have htan_c : phi p d x₀ + s * (c - x₀) ≤ phi p d c := htan c hcIcc
    have hsm : s * (x - c) ≤ m * (x - c) := by nlinarith [hms, hxc]
    have hmin_x := hmin x hx
    linarith [htan_c, hsm, hmin_x]

/-- **Supporting line on the left convex piece.**  Mirror of `supportingLine_right_of_convex`
for `x₀ ∈ (0,c)` with `φ_{p,d}'' > 0` on `(0,c)` and an affine minorant tangent at `c`. -/
theorem supportingLine_left_of_convex {d : ℕ} {p c x₀ : ℝ}
    (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    (hx₀0 : 0 < x₀) (hx₀c : x₀ < c) (hc1 : c < 1)
    (hconv : ∀ x ∈ Set.Ioo (0:ℝ) c, 0 < phi'' p d x)
    (hmin : ∀ x ∈ Set.Icc (0:ℝ) 1, phi p d c + deriv (phi p d) c * (x - c) ≤ phi p d x) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, phi p d x₀ + deriv (phi p d) x₀ * (x - x₀) ≤ phi p d x := by
  have hc0 : 0 < c := lt_trans hx₀0 hx₀c
  have hcont : ContinuousOn (phi p d) (Set.Icc 0 c) :=
    (phi_continuousOn_Icc hd hp0 hp1).mono (Set.Icc_subset_Icc le_rfl hc1.le)
  have hdiff : DifferentiableOn ℝ (phi p d) (interior (Set.Icc 0 c)) := by
    rw [interior_Icc]; intro x hx
    exact (hasDerivAt_phi hd hp0 hp1 hx.1 (lt_trans hx.2 hc1)).differentiableAt.differentiableWithinAt
  have hdiff2 : DifferentiableOn ℝ (deriv (phi p d)) (interior (Set.Icc 0 c)) := by
    rw [interior_Icc]; intro x hx
    exact (hasDerivAt_phi'' hd hp0 hp1 hx.1 (lt_trans hx.2 hc1)).differentiableAt.differentiableWithinAt
  have hnn : ∀ x ∈ interior (Set.Icc 0 c), 0 ≤ deriv^[2] (phi p d) x := by
    rw [interior_Icc]; intro x hx
    have he : deriv^[2] (phi p d) x = phi'' p d x := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact (hasDerivAt_phi'' hd hp0 hp1 hx.1 (lt_trans hx.2 hc1)).deriv
    rw [he]; exact (hconv x hx).le
  have hconvex : ConvexOn ℝ (Set.Icc 0 c) (phi p d) :=
    convexOn_of_deriv2_nonneg (convex_Icc 0 c) hcont hdiff hdiff2 hnn
  have hHx₀ : HasDerivAt (phi p d) (deriv (phi p d) x₀) x₀ := by
    have h := hasDerivAt_phi hd hp0 hp1 hx₀0 (lt_trans hx₀c hc1); rw [h.deriv]; exact h
  have hHc : HasDerivAt (phi p d) (deriv (phi p d) c) c := by
    have h := hasDerivAt_phi hd hp0 hp1 hc0 hc1; rw [h.deriv]; exact h
  have hx₀Icc : x₀ ∈ Set.Icc (0:ℝ) c := ⟨hx₀0.le, hx₀c.le⟩
  have hcIcc : c ∈ Set.Icc (0:ℝ) c := ⟨hc0.le, le_refl c⟩
  set s := deriv (phi p d) x₀ with hs
  set m := deriv (phi p d) c with hmm
  have htan : ∀ y ∈ Set.Icc (0:ℝ) c, phi p d x₀ + s * (y - x₀) ≤ phi p d y :=
    convexOn_tangent_le hconvex hx₀Icc hHx₀
  have hsm_le : s ≤ m := by
    have h1 := hconvex.le_slope_of_hasDerivAt hx₀Icc hcIcc hx₀c hHx₀
    have h2 := hconvex.slope_le_of_hasDerivAt hx₀Icc hcIcc hx₀c hHc
    exact le_trans h1 h2
  intro x hx
  rcases le_total x c with hxc | hcx
  · exact htan x ⟨hx.1, hxc⟩
  · have htan_c : phi p d x₀ + s * (c - x₀) ≤ phi p d c := htan c hcIcc
    have hsm : s * (x - c) ≤ m * (x - c) := by nlinarith [hsm_le, hcx]
    have hmin_x := hmin x hx
    linarith [htan_c, hsm, hmin_x]

/-- `φ_{p,d}'' > 0` to the right of the right contact `b` (`r_* < b`, `0 < h_{p,d}(b)`):
on `(b^d, 1)` the convexity defect `h_{p,d}` exceeds its positive value at `b`. -/
theorem phi''_pos_right_of_contact {d : ℕ} (hd : 2 ≤ d) {p b : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hbs : rStar d < b) (hb1 : b < 1) (hhb : 0 < hpd p d b) :
    ∀ x ∈ Set.Ioo (b ^ d) 1, 0 < phi'' p d x := by
  intro x hx
  have hb0 : 0 < b := lt_trans (rStar_pos hd) hbs
  have hx0 : 0 < x := lt_trans (pow_pos hb0 d) hx.1
  have hzpos : (0:ℝ) < 1 / (d:ℝ) := by have := dpos hd; positivity
  have hbeq : Real.rpow (b ^ d) (1/(d:ℝ)) = b := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hb0.le (by omega)
  have hub : b < Real.rpow x (1/(d:ℝ)) := by
    rw [← hbeq]; exact Real.rpow_lt_rpow (pow_nonneg hb0.le d) hx.1 hzpos
  have hu1 : Real.rpow x (1/(d:ℝ)) < 1 := by
    have h : Real.rpow x (1/(d:ℝ)) < Real.rpow 1 (1/(d:ℝ)) := Real.rpow_lt_rpow hx0.le hx.2 hzpos
    simpa using h
  rw [phi''_pos_iff hd hx0]
  have hmono := hpd_strictMonoOn hd hp0 hp1 ⟨hbs, hb1⟩ ⟨lt_trans hbs hub, hu1⟩ hub
  linarith [hhb, hmono]

/-- `φ_{p,d}'' > 0` to the left of the left contact `a` (`a < r_*`, `0 < h_{p,d}(a)`). -/
theorem phi''_pos_left_of_contact {d : ℕ} (hd : 2 ≤ d) {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 < a) (has : a < rStar d) (hha : 0 < hpd p d a) :
    ∀ x ∈ Set.Ioo (0:ℝ) (a ^ d), 0 < phi'' p d x := by
  intro x hx
  have hx0 : 0 < x := hx.1
  have hzpos : (0:ℝ) < 1 / (d:ℝ) := by have := dpos hd; positivity
  have haeq : Real.rpow (a ^ d) (1/(d:ℝ)) = a := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast ha0.le (by omega)
  have hua : Real.rpow x (1/(d:ℝ)) < a := by
    rw [← haeq]; exact Real.rpow_lt_rpow hx0.le hx.2 hzpos
  have hu0 : 0 < Real.rpow x (1/(d:ℝ)) := Real.rpow_pos_of_pos hx0 _
  rw [phi''_pos_iff hd hx0]
  have hanti := hpd_strictAntiOn hd hp0 hp1 ⟨hu0, lt_trans hua has⟩ ⟨ha0, has⟩ hua
  linarith [hha, hanti]

/-- A strictly convex function lies *strictly* above its tangent line away from the point
of tangency. -/
theorem strictConvexOn_tangent_lt {S : Set ℝ} {f : ℝ → ℝ} {f' x₀ : ℝ}
    (hfc : StrictConvexOn ℝ S f) (hx₀ : x₀ ∈ S) (hderiv : HasDerivAt f f' x₀) :
    ∀ y ∈ S, y ≠ x₀ → f x₀ + f' * (y - x₀) < f y := by
  intro y hy hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := hfc.slope_lt_of_hasDerivAt hy hx₀ hlt hderiv
    rw [_root_.slope_def_field] at h
    have hpos : 0 < x₀ - y := by linarith
    rw [div_lt_iff₀ hpos] at h
    linarith
  · have h := hfc.lt_slope_of_hasDerivAt hx₀ hy hgt hderiv
    rw [_root_.slope_def_field] at h
    have hpos : 0 < y - x₀ := by linarith
    rw [lt_div_iff₀ hpos] at h
    linarith

/-- **Strict supporting line on the right convex piece.**  Strengthens
`supportingLine_right_of_convex` to a strict inequality away from `x₀`. -/
theorem supportingLine_right_of_convex_strict {d : ℕ} {p c x₀ : ℝ}
    (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    (hc0 : 0 < c) (hcx₀ : c < x₀) (hx₀1 : x₀ < 1)
    (hconv : ∀ x ∈ Set.Ioo c 1, 0 < phi'' p d x)
    (hmin : ∀ x ∈ Set.Icc (0:ℝ) 1, phi p d c + deriv (phi p d) c * (x - c) ≤ phi p d x) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, x ≠ x₀ →
      phi p d x₀ + deriv (phi p d) x₀ * (x - x₀) < phi p d x := by
  have hc1 : c < 1 := lt_trans hcx₀ hx₀1
  have hsconv : StrictConvexOn ℝ (Set.Icc c 1) (phi p d) :=
    strictConvexOn_phi_right hd hp0 hp1 hc0 hc1 hconv
  have hHx₀ : HasDerivAt (phi p d) (deriv (phi p d) x₀) x₀ := by
    have h := hasDerivAt_phi hd hp0 hp1 (lt_trans hc0 hcx₀) hx₀1; rw [h.deriv]; exact h
  have hHc : HasDerivAt (phi p d) (deriv (phi p d) c) c := by
    have h := hasDerivAt_phi hd hp0 hp1 hc0 hc1; rw [h.deriv]; exact h
  have hx₀Icc : x₀ ∈ Set.Icc c 1 := ⟨hcx₀.le, hx₀1.le⟩
  have hcIcc : c ∈ Set.Icc c 1 := ⟨le_refl c, hc1.le⟩
  set s := deriv (phi p d) x₀ with hs
  set m := deriv (phi p d) c with hmm
  -- `m < s` (strict, from strict convexity)
  have hms : m < s := by
    have h1 := hsconv.lt_slope_of_hasDerivAt hcIcc hx₀Icc hcx₀ hHc
    have h2 := hsconv.slope_lt_of_hasDerivAt hcIcc hx₀Icc hcx₀ hHx₀
    exact lt_trans h1 h2
  intro x hx hne
  rcases lt_or_ge x c with hxc | hcx
  · -- `x < c`: glue strictly through the affine minorant
    have htan_c : phi p d x₀ + s * (c - x₀) < phi p d c :=
      strictConvexOn_tangent_lt hsconv hx₀Icc hHx₀ c hcIcc (ne_of_lt hcx₀)
    have hsm : s * (x - c) < m * (x - c) := by nlinarith [hms, hxc]
    have hmin_x := hmin x hx
    linarith [htan_c, hsm, hmin_x]
  · -- `x ≥ c`: strict convexity directly
    exact strictConvexOn_tangent_lt hsconv hx₀Icc hHx₀ x ⟨hcx, hx.2⟩ hne

/-- **Strict supporting line on the left convex piece.** -/
theorem supportingLine_left_of_convex_strict {d : ℕ} {p c x₀ : ℝ}
    (hd : 2 ≤ d) (hp0 : 0 < p) (hp1 : p < 1)
    (hx₀0 : 0 < x₀) (hx₀c : x₀ < c) (hc1 : c < 1)
    (hconv : ∀ x ∈ Set.Ioo (0:ℝ) c, 0 < phi'' p d x)
    (hmin : ∀ x ∈ Set.Icc (0:ℝ) 1, phi p d c + deriv (phi p d) c * (x - c) ≤ phi p d x) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, x ≠ x₀ →
      phi p d x₀ + deriv (phi p d) x₀ * (x - x₀) < phi p d x := by
  have hc0 : 0 < c := lt_trans hx₀0 hx₀c
  have hsconv : StrictConvexOn ℝ (Set.Icc 0 c) (phi p d) :=
    strictConvexOn_phi_left hd hp0 hp1 hc0 hc1 hconv
  have hHx₀ : HasDerivAt (phi p d) (deriv (phi p d) x₀) x₀ := by
    have h := hasDerivAt_phi hd hp0 hp1 hx₀0 (lt_trans hx₀c hc1); rw [h.deriv]; exact h
  have hHc : HasDerivAt (phi p d) (deriv (phi p d) c) c := by
    have h := hasDerivAt_phi hd hp0 hp1 hc0 hc1; rw [h.deriv]; exact h
  have hx₀Icc : x₀ ∈ Set.Icc (0:ℝ) c := ⟨hx₀0.le, hx₀c.le⟩
  have hcIcc : c ∈ Set.Icc (0:ℝ) c := ⟨hc0.le, le_refl c⟩
  set s := deriv (phi p d) x₀ with hs
  set m := deriv (phi p d) c with hmm
  have hsm_lt : s < m := by
    have h1 := hsconv.lt_slope_of_hasDerivAt hx₀Icc hcIcc hx₀c hHx₀
    have h2 := hsconv.slope_lt_of_hasDerivAt hx₀Icc hcIcc hx₀c hHc
    exact lt_trans h1 h2
  intro x hx hne
  rcases le_or_gt x c with hxc | hcx
  · -- `x ≤ c`: strict convexity directly
    exact strictConvexOn_tangent_lt hsconv hx₀Icc hHx₀ x ⟨hx.1, hxc⟩ hne
  · -- `x > c`: glue strictly through the affine minorant
    have htan_c : phi p d x₀ + s * (c - x₀) < phi p d c :=
      strictConvexOn_tangent_lt hsconv hx₀Icc hHx₀ c hcIcc (ne_of_gt hx₀c)
    have hsm : s * (x - c) < m * (x - c) := by nlinarith [hsm_lt, hcx]
    have hmin_x := hmin x hx
    linarith [htan_c, hsm, hmin_x]

/-- **Quadratic lower bound from a second-derivative bound** (the Taylor heart of M4).
If `f` is `C²` on `[a,b]` with `f'' ≥ m`, and both `f` and `f'` vanish at an interior
point `c`, then `f(x) ≥ (m/2)(x-c)²` throughout `[a,b]`.  Proof: `g := f − (m/2)(·−c)²`
has `g'' = f'' − m ≥ 0`, so `g'` is monotone; since `g'(c) = 0`, `g` is antitone left of
`c` and monotone right of `c`, hence `g ≥ g(c) = 0`.  Applied to the supporting-line gap
`g_r = φ_{p_r} − ℓ_r` (which has `g_r = g_r' = 0` at each contact, `g_r'' = φ_{p_r}'' ≥ m_K`
on the strictly-convex windows) this gives the near-contact half of `quadSep`. -/
theorem quadratic_lower_of_deriv2_ge {f f' f'' : ℝ → ℝ} {c m a b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x)
    (hge : ∀ x ∈ Set.Icc a b, m ≤ f'' x)
    (hfc : f c = 0) (hf'c : f' c = 0) :
    ∀ x ∈ Set.Icc a b, m / 2 * (x - c) ^ 2 ≤ f x := by
  set g : ℝ → ℝ := fun x => f x - m / 2 * (x - c) ^ 2 with hg
  set g' : ℝ → ℝ := fun x => f' x - m * (x - c) with hg'
  have hgderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x := by
    intro x hx
    have h2 : HasDerivAt (fun y : ℝ => m / 2 * (y - c) ^ 2) (m * (x - c)) x := by
      have hp : HasDerivAt (fun y : ℝ => (y - c) ^ 2) (2 * (x - c)) x := by
        have := ((hasDerivAt_id x).sub_const c).fun_pow 2
        simpa using this
      have h := hp.const_mul (m / 2)
      rw [show m * (x - c) = m / 2 * (2 * (x - c)) from by ring]
      exact h
    have := (hf x hx).fun_sub h2
    simpa only [hg, hg'] using this
  have hg'deriv : ∀ x ∈ Set.Icc a b, HasDerivAt g' (f'' x - m) x := by
    intro x hx
    have h2 : HasDerivAt (fun y : ℝ => m * (y - c)) m x := by
      have := ((hasDerivAt_id x).sub_const c).const_mul m
      simpa using this
    have := (hf' x hx).fun_sub h2
    simpa only [hg'] using this
  have hg'_mono : MonotoneOn g' (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x hx => (hg'deriv x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg'deriv x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hxmem : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    rw [(hg'deriv x hxmem).deriv]; linarith [hge x hxmem]
  have hg'c : g' c = 0 := by simp only [hg', hf'c]; ring
  have hgc : g c = 0 := by simp only [hg, hfc]; ring
  have hmono : MonotoneOn g (Set.Icc c b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c b)
      (fun x hx => (hgderiv x ⟨le_trans hac hx.1, hx.2⟩).continuousAt.continuousWithinAt)
      (fun x hx => (hgderiv x ⟨le_trans hac (interior_subset hx).1,
        (interior_subset hx).2⟩).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hxab : x ∈ Set.Icc a b := ⟨le_trans hac (le_of_lt hx.1), le_of_lt hx.2⟩
    rw [(hgderiv x hxab).deriv]
    have := hg'_mono ⟨hac, hcb⟩ hxab (le_of_lt hx.1)
    rw [hg'c] at this; exact this
  have hanti : AntitoneOn g (Set.Icc a c) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a c)
      (fun x hx => (hgderiv x ⟨hx.1, le_trans hx.2 hcb⟩).continuousAt.continuousWithinAt)
      (fun x hx => (hgderiv x ⟨(interior_subset hx).1,
        le_trans (interior_subset hx).2 hcb⟩).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hxab : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) hcb⟩
    rw [(hgderiv x hxab).deriv]
    have := hg'_mono hxab ⟨hac, hcb⟩ (le_of_lt hx.2)
    rw [hg'c] at this; exact this
  intro x hx
  have hgx : 0 ≤ g x := by
    rcases le_total x c with hxc | hcx
    · have := hanti ⟨hx.1, hxc⟩ ⟨hac, le_refl c⟩ hxc
      rw [hgc] at this; exact this
    · have := hmono ⟨le_refl c, hcb⟩ ⟨hcx, hx.2⟩ hcx
      rw [hgc] at this; exact this
  simp only [hg] at hgx; linarith

/-! ### M4 joint-continuity foundations -/

/-- Joint continuity of `h_{p,d}` in `(p,u)` on `(0,1)×(0,1)`. -/
theorem hpd_continuousOn_prod {d : ℕ} :
    ContinuousOn (fun q : ℝ × ℝ => hpd q.1 d q.2)
      (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) := by
  have hfst : ContinuousOn (fun q : ℝ × ℝ => q.1) (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) :=
    continuous_fst.continuousOn
  have hsnd : ContinuousOn (fun q : ℝ × ℝ => q.2) (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) :=
    continuous_snd.continuousOn
  unfold hpd Jp'' Jp'
  apply ContinuousOn.sub
  · -- `q.2 * (1 / (q.2 * (1 - q.2)))`
    refine hsnd.mul (continuousOn_const.div (hsnd.mul (continuousOn_const.sub hsnd)) ?_)
    intro q hq
    obtain ⟨_, hu⟩ := Set.mem_prod.mp hq
    exact ne_of_gt (mul_pos hu.1 (by linarith [hu.2]))
  · -- `(d-1) * log (q.2*(1-q.1)/((1-q.2)*q.1))`
    refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
    · refine (hsnd.mul (continuousOn_const.sub hfst)).div
        ((continuousOn_const.sub hsnd).mul hfst) ?_
      intro q hq
      obtain ⟨hp, hu⟩ := Set.mem_prod.mp hq
      exact ne_of_gt (mul_pos (by linarith [hu.2]) hp.1)
    · intro q hq
      obtain ⟨hp, hu⟩ := Set.mem_prod.mp hq
      exact ne_of_gt (div_pos (mul_pos hu.1 (by linarith [hp.2])) (mul_pos (by linarith [hu.2]) hp.1))

/-- Joint continuity of `φ_{p,d}''` in `(p,x)` on `(0,1)×(0,1)`. -/
theorem phi''_continuousOn_prod {d : ℕ} (hd : 2 ≤ d) :
    ContinuousOn (fun q : ℝ × ℝ => phi'' q.1 d q.2)
      (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) := by
  set S := Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1 with hS
  have hc : (0:ℝ) < 1/(d:ℝ) := by have := dpos hd; positivity
  have hU : ContinuousOn (fun q : ℝ × ℝ => Real.rpow q.2 (1/(d:ℝ))) S := by
    apply ContinuousOn.rpow_const continuous_snd.continuousOn
    intro q hq; left; obtain ⟨_, hu⟩ := Set.mem_prod.mp hq; exact ne_of_gt hu.1
  have hUmem : ∀ q ∈ S, Real.rpow q.2 (1/(d:ℝ)) ∈ Set.Ioo (0:ℝ) 1 := by
    intro q hq; obtain ⟨_, hu⟩ := Set.mem_prod.mp hq
    exact ⟨Real.rpow_pos_of_pos hu.1 _, Real.rpow_lt_one hu.1.le hu.2 hc⟩
  have hpair : ContinuousOn (fun q : ℝ × ℝ => (q.1, Real.rpow q.2 (1/(d:ℝ)))) S :=
    continuous_fst.continuousOn.prodMk hU
  have hpairmaps : Set.MapsTo (fun q : ℝ × ℝ => (q.1, Real.rpow q.2 (1/(d:ℝ)))) S S := by
    intro q hq; obtain ⟨hp, _⟩ := Set.mem_prod.mp hq
    exact Set.mem_prod.mpr ⟨hp, hUmem q hq⟩
  have hnum : ContinuousOn (fun q : ℝ × ℝ => hpd q.1 d (Real.rpow q.2 (1/(d:ℝ)))) S :=
    hpd_continuousOn_prod.comp hpair hpairmaps
  have hden : ContinuousOn
      (fun q : ℝ × ℝ => (d:ℝ)^2 * (Real.rpow q.2 (1/(d:ℝ)))^(2*d-1)) S :=
    continuousOn_const.mul (hU.pow (2*d-1))
  unfold phi''
  refine hnum.div hden ?_
  intro q hq
  have hu := hUmem q hq
  have hdpos := dpos hd
  have hu0 := hu.1
  exact ne_of_gt (by positivity)

/-- Joint continuity of `J_p(u)` in `(p,u)` on `(0,1)×(0,1)`. -/
theorem Jp_continuousOn_prod :
    ContinuousOn (fun q : ℝ × ℝ => Jp q.1 q.2)
      (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) := by
  have hfst : ContinuousOn (fun q : ℝ × ℝ => q.1) (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) :=
    continuous_fst.continuousOn
  have hsnd : ContinuousOn (fun q : ℝ × ℝ => q.2) (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) :=
    continuous_snd.continuousOn
  unfold Jp
  apply ContinuousOn.add
  · refine hsnd.mul (ContinuousOn.log (hsnd.div hfst ?_) ?_)
    · intro q hq; obtain ⟨hp, _⟩ := Set.mem_prod.mp hq; exact ne_of_gt hp.1
    · intro q hq; obtain ⟨hp, hu⟩ := Set.mem_prod.mp hq
      exact ne_of_gt (div_pos hu.1 hp.1)
  · refine (continuousOn_const.sub hsnd).mul
      (ContinuousOn.log ((continuousOn_const.sub hsnd).div (continuousOn_const.sub hfst) ?_) ?_)
    · intro q hq; obtain ⟨hp, _⟩ := Set.mem_prod.mp hq; exact ne_of_gt (by linarith [hp.2])
    · intro q hq; obtain ⟨hp, hu⟩ := Set.mem_prod.mp hq
      exact ne_of_gt (div_pos (by linarith [hu.2]) (by linarith [hp.2]))

/-- Joint continuity of `φ_{p,d}(x)` in `(p,x)` on `(0,1)×(0,1)`. -/
theorem phi_continuousOn_prod {d : ℕ} (hd : 2 ≤ d) :
    ContinuousOn (fun q : ℝ × ℝ => phi q.1 d q.2)
      (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) := by
  set S := Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1 with hS
  have hc : (0:ℝ) < 1/(d:ℝ) := by have := dpos hd; positivity
  have hU : ContinuousOn (fun q : ℝ × ℝ => Real.rpow q.2 (1/(d:ℝ))) S := by
    apply ContinuousOn.rpow_const continuous_snd.continuousOn
    intro q hq; left; obtain ⟨_, hu⟩ := Set.mem_prod.mp hq; exact ne_of_gt hu.1
  have hUmem : ∀ q ∈ S, Real.rpow q.2 (1/(d:ℝ)) ∈ Set.Ioo (0:ℝ) 1 := by
    intro q hq; obtain ⟨_, hu⟩ := Set.mem_prod.mp hq
    exact ⟨Real.rpow_pos_of_pos hu.1 _, Real.rpow_lt_one hu.1.le hu.2 hc⟩
  have hpair : ContinuousOn (fun q : ℝ × ℝ => (q.1, Real.rpow q.2 (1/(d:ℝ)))) S :=
    continuous_fst.continuousOn.prodMk hU
  have hpairmaps : Set.MapsTo (fun q : ℝ × ℝ => (q.1, Real.rpow q.2 (1/(d:ℝ)))) S S := by
    intro q hq; obtain ⟨hp, _⟩ := Set.mem_prod.mp hq
    exact Set.mem_prod.mpr ⟨hp, hUmem q hq⟩
  exact Jp_continuousOn_prod.comp hpair hpairmaps

set_option maxHeartbeats 1000000 in
/-- **Uniform strictly-convex window around a contact curve.**  Given a compact `K`,
continuous `pc, c : K → (0,1)` with `φ''_{pc r}(c r) > 0`, there is a uniform window
radius `η > 0` and lower bound `m_K > 0` so that `φ''_{pc r}(x) ≥ m_K` for all `r ∈ K`
and `x` within `η` of `c r` (and such `x ∈ (0,1)`).  This is the tube/Heine–Cantor step
of `quadSep`. -/
theorem uniform_phi''_window {d : ℕ} (hd : 2 ≤ d) {K : Set ℝ} (hK : IsCompact K)
    (hKne : K.Nonempty) {pc c : ℝ → ℝ} (hpc : ContinuousOn pc K) (hc : ContinuousOn c K)
    (hpc_mem : ∀ r ∈ K, pc r ∈ Set.Ioo (0:ℝ) 1)
    (hc_mem : ∀ r ∈ K, c r ∈ Set.Ioo (0:ℝ) 1)
    (hpos : ∀ r ∈ K, 0 < phi'' (pc r) d (c r)) :
    ∃ η m_K : ℝ, 0 < η ∧ 0 < m_K ∧ ∀ r ∈ K, ∀ x ∈ Set.Icc (c r - η) (c r + η),
      (0 < x ∧ x < 1) ∧ m_K ≤ phi'' (pc r) d x := by
  -- uniform bounds `α ≤ c r ≤ β`, `0 < α`, `β < 1`
  obtain ⟨rmin, hrmin, hcmin⟩ := hK.exists_isMinOn hKne hc
  obtain ⟨rmax, hrmax, hcmax⟩ := hK.exists_isMaxOn hKne hc
  set α := c rmin with hαdef
  set β := c rmax with hβdef
  have hα0 : 0 < α := (hc_mem rmin hrmin).1
  have hβ1 : β < 1 := (hc_mem rmax hrmax).2
  have hcα : ∀ r ∈ K, α ≤ c r := fun r hr => isMinOn_iff.mp hcmin r hr
  have hcβ : ∀ r ∈ K, c r ≤ β := fun r hr => isMaxOn_iff.mp hcmax r hr
  have hαβ : α ≤ β := hcβ rmin hrmin
  -- `m₀ = min φ''(pc r)(c r) > 0`
  have hG_cont : ContinuousOn (fun r => phi'' (pc r) d (c r)) K := by
    have hmaps : Set.MapsTo (fun r => (pc r, c r)) K (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) :=
      fun r hr => Set.mem_prod.mpr ⟨hpc_mem r hr, hc_mem r hr⟩
    exact (phi''_continuousOn_prod hd).comp (hpc.prodMk hc) hmaps
  obtain ⟨m₀, hm₀0, hm₀le⟩ := hK.exists_forall_le' hG_cont hpos
  -- compact strip `T = K × [lo, hi]` inside `(0,1)`
  set lo := α/2 with hlodef
  set hi := (1+β)/2 with hhidef
  have hlo0 : 0 < lo := by rw [hlodef]; linarith
  have hhi1 : hi < 1 := by rw [hhidef]; linarith
  have hlohi : lo ≤ hi := by rw [hlodef, hhidef]; linarith
  set T := K ×ˢ Set.Icc lo hi with hTdef
  have hTcompact : IsCompact T := hK.prod isCompact_Icc
  have hG2_cont : ContinuousOn (fun q : ℝ × ℝ => phi'' (pc q.1) d q.2) T := by
    have hfst : Set.MapsTo (fun q : ℝ × ℝ => q.1) T K :=
      fun q hq => (Set.mem_prod.mp hq).1
    have hpc1 : ContinuousOn (fun q : ℝ × ℝ => pc q.1) T :=
      hpc.comp continuous_fst.continuousOn hfst
    have hpair : ContinuousOn (fun q : ℝ × ℝ => (pc q.1, q.2)) T :=
      hpc1.prodMk continuous_snd.continuousOn
    have hmaps : Set.MapsTo (fun q : ℝ × ℝ => (pc q.1, q.2)) T
        (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) := by
      intro q hq
      obtain ⟨hqK, hqIcc⟩ := Set.mem_prod.mp hq
      exact Set.mem_prod.mpr ⟨hpc_mem q.1 hqK, ⟨lt_of_lt_of_le hlo0 hqIcc.1,
        lt_of_le_of_lt hqIcc.2 hhi1⟩⟩
    exact (phi''_continuousOn_prod hd).comp hpair hmaps
  have hUC := (hTcompact.uniformContinuousOn_of_continuous hG2_cont)
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδ0, hδ⟩ := hUC (m₀/2) (by linarith)
  set η := min (δ/2) (min (α/2) ((1-β)/2)) with hηdef
  have hη0 : 0 < η := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hηδ : η ≤ δ/2 := min_le_left _ _
  have hηα : η ≤ α/2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηβ : η ≤ (1-β)/2 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨η, m₀/2, hη0, by linarith, ?_⟩
  intro r hr x hx
  have hcr_α : α ≤ c r := hcα r hr
  have hcr_β : c r ≤ β := hcβ r hr
  have hx0 : 0 < x := by have := hx.1; linarith
  have hx1 : x < 1 := by have := hx.2; linarith
  have hxlo : lo ≤ x := by rw [hlodef]; have := hx.1; linarith
  have hxhi : x ≤ hi := by rw [hhidef]; have := hx.2; linarith
  have hcrlo : lo ≤ c r := by rw [hlodef]; linarith
  have hcrhi : c r ≤ hi := by rw [hhidef]; linarith
  have hmem1 : (r, x) ∈ T := Set.mem_prod.mpr ⟨hr, ⟨hxlo, hxhi⟩⟩
  have hmem2 : (r, c r) ∈ T := Set.mem_prod.mpr ⟨hr, ⟨hcrlo, hcrhi⟩⟩
  have hdist : dist (r, x) (r, c r) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    have hxcr : |x - c r| ≤ η := by
      rw [abs_sub_le_iff]; exact ⟨by have := hx.2; linarith, by have := hx.1; linarith⟩
    simp only [max_lt_iff]
    exact ⟨by linarith, by linarith⟩
  have hcmp := hδ (r, x) hmem1 (r, c r) hmem2 hdist
  rw [Real.dist_eq] at hcmp
  have hm₀cr : m₀ ≤ phi'' (pc r) d (c r) := hm₀le r hr
  refine ⟨⟨hx0, hx1⟩, ?_⟩
  have := abs_lt.mp hcmp
  linarith [this.1, this.2]

/-- **Strict positivity of the supporting-line gap off the contacts** (abstract form).
For a Lubetzky–Zhao contact pair `xa < xb` at parameter `p` (common tangent slope `m`, chord
equation, the affine minorant `L`, strictly-convex pieces `(0,xa)`/`(xb,1)`, and
`lce < φ` strictly between), the gap `φ_{p,d}(x) − L(x)` is `> 0` for every
`x ∈ [0,1] ∖ {xa, xb}`. -/
theorem gap_pos_abstract {d : ℕ} (hd : 2 ≤ d) {p xa xb m : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hxa0 : 0 < xa) (hxa_xb : xa < xb) (hxb1 : xb < 1)
    (hHxa : HasDerivAt (phi p d) m xa) (hHxb : HasDerivAt (phi p d) m xb)
    (hchord : phi p d xb = phi p d xa + m * (xb - xa))
    (hsupp : ∀ t ∈ Set.Icc (0:ℝ) 1, phi p d xa + m * (t - xa) ≤ phi p d t)
    (hconvL : ∀ y ∈ Set.Ioo (0:ℝ) xa, 0 < phi'' p d y)
    (hconvR : ∀ y ∈ Set.Ioo xb 1, 0 < phi'' p d y)
    (hlce : ∀ x ∈ Set.Ioo xa xb, lce 0 1 (phi p d) x < phi p d x)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hne1 : x ≠ xa) (hne2 : x ≠ xb) :
    0 < phi p d x - (phi p d xa + m * (x - xa)) := by
  have hxb0 : 0 < xb := lt_trans hxa0 hxa_xb
  have hxa1 : xa < 1 := lt_trans hxa_xb hxb1
  rcases lt_trichotomy x xa with hlt | heq | hgt
  · have hsconv : StrictConvexOn ℝ (Set.Icc 0 xa) (phi p d) :=
      strictConvexOn_phi_left hd hp0 hp1 hxa0 hxa1 hconvL
    have h := strictConvexOn_tangent_lt hsconv ⟨hxa0.le, le_refl xa⟩ hHxa x ⟨hx0, hlt.le⟩
      (ne_of_lt hlt)
    linarith [h]
  · exact absurd heq hne1
  · rcases lt_trichotomy x xb with hlt2 | heq2 | hgt2
    · have h1 : lce 0 1 (phi p d) x < phi p d x := hlce x ⟨hgt, hlt2⟩
      have hmin : ∀ t ∈ Set.Icc (0:ℝ) 1, m * t + (phi p d xa - m * xa) ≤ phi p d t := by
        intro t ht; have h := hsupp t ht; linarith
      have h2 : m * x + (phi p d xa - m * xa) ≤ lce 0 1 (phi p d) x :=
        affine_le_lce hmin ⟨hx0, hx1⟩
      nlinarith [h1, h2]
    · exact absurd heq2 hne2
    · have hsconv : StrictConvexOn ℝ (Set.Icc xb 1) (phi p d) :=
        strictConvexOn_phi_right hd hp0 hp1 hxb0 hxb1 hconvR
      have h := strictConvexOn_tangent_lt hsconv ⟨le_refl xb, hxb1.le⟩ hHxb x ⟨hgt2.le, hx1⟩
        (ne_of_gt hgt2)
      -- `φ(xb) + m(x-xb) < φ(x)` and `L(x) = φ(xb) + m(x-xb)` via the chord
      nlinarith [h, hchord]

/-- **Per-`p` contact data bundle.**  Packages everything the `quadSep` estimates need at the
Lubetzky–Zhao contacts `xa = (u_a p)^d < xb = (u_b p)^d`: the common tangent (`HasDerivAt φ m`
at both, `m = φ'(xa)`), the chord equation, the affine minorant (`L ≤ φ`), the
strictly-convex pieces (`φ''>0` on `(0,xa)` and `(xb,1)`, and `φ''>0` at the contacts),
and `lce < φ` strictly between. -/
theorem contact_bundle {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {p : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) :
    0 < (G.ua p) ^ d ∧ (G.ua p) ^ d < (G.ub p) ^ d ∧ (G.ub p) ^ d < 1 ∧
    HasDerivAt (phi p d) (deriv (phi p d) ((G.ua p) ^ d)) ((G.ua p) ^ d) ∧
    HasDerivAt (phi p d) (deriv (phi p d) ((G.ua p) ^ d)) ((G.ub p) ^ d) ∧
    phi p d ((G.ub p) ^ d)
      = phi p d ((G.ua p) ^ d) + deriv (phi p d) ((G.ua p) ^ d) * ((G.ub p) ^ d - (G.ua p) ^ d) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1,
      phi p d ((G.ua p) ^ d) + deriv (phi p d) ((G.ua p) ^ d) * (t - (G.ua p) ^ d) ≤ phi p d t) ∧
    (∀ y ∈ Set.Ioo (0:ℝ) ((G.ua p) ^ d), 0 < phi'' p d y) ∧
    (∀ y ∈ Set.Ioo ((G.ub p) ^ d) 1, 0 < phi'' p d y) ∧
    (∀ x ∈ Set.Ioo ((G.ua p) ^ d) ((G.ub p) ^ d), lce 0 1 (phi p d) x < phi p d x) ∧
    0 < phi'' p d ((G.ua p) ^ d) ∧ 0 < phi'' p d ((G.ub p) ^ d) := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  obtain ⟨hua0, huas, hubs, hub1, hcf, hhua, hhub⟩ := G.contact p hp0 hp
  have hub0 : 0 < G.ub p := lt_trans (rStar_pos hd) hubs
  have hua1 : G.ua p < 1 := lt_trans huas (rStar_lt_one hd)
  have hxa0 : 0 < (G.ua p) ^ d := pow_pos hua0 d
  have hxb1 : (G.ub p) ^ d < 1 := pow_lt_one₀ hub0.le hub1 (by omega)
  have hxa_xb : (G.ua p) ^ d < (G.ub p) ^ d :=
    pow_lt_pow_left₀ (lt_trans huas hubs) hua0.le (by omega)
  have hxa1 : (G.ua p) ^ d < 1 := lt_trans hxa_xb hxb1
  have hxb0 : 0 < (G.ub p) ^ d := lt_trans hxa0 hxa_xb
  -- common tangent slope `m = φ'(xa) = φ'(xb)`
  have hma : deriv (phi p d) ((G.ua p) ^ d) = sCM d p (G.ua p) :=
    deriv_phi_pow_eq_sCM hd hp0 hp1 hua0 hua1
  have hmb : deriv (phi p d) ((G.ub p) ^ d) = sCM d p (G.ub p) :=
    deriv_phi_pow_eq_sCM hd hp0 hp1 hub0 hub1
  have hslope_eq : deriv (phi p d) ((G.ua p) ^ d) = deriv (phi p d) ((G.ub p) ^ d) := by
    have hx := (Prod.ext_iff.mp hcf).1; simp only [contactF, Prod.fst_zero] at hx
    rw [hma, hmb]; linarith
  have hHxa : HasDerivAt (phi p d) (deriv (phi p d) ((G.ua p) ^ d)) ((G.ua p) ^ d) := by
    have h := hasDerivAt_phi hd hp0 hp1 hxa0 hxa1; rw [h.deriv]; exact h
  have hHxb : HasDerivAt (phi p d) (deriv (phi p d) ((G.ua p) ^ d)) ((G.ub p) ^ d) := by
    have h := hasDerivAt_phi hd hp0 hp1 hxb0 hxb1; rw [hslope_eq, h.deriv]; exact h
  have hchord : phi p d ((G.ub p) ^ d)
      = phi p d ((G.ua p) ^ d)
        + deriv (phi p d) ((G.ua p) ^ d) * ((G.ub p) ^ d - (G.ua p) ^ d) := by
    have hx := (Prod.ext_iff.mp hcf).2; simp only [contactF, Prod.snd_zero] at hx
    have hja : phi p d ((G.ua p) ^ d) = Jp p (G.ua p) := phi_pow_eq_Jp hd hua0
    have hjb : phi p d ((G.ub p) ^ d) = Jp p (G.ub p) := phi_pow_eq_Jp hd hub0
    rw [hja, hjb, hma]; linarith
  have hsupp : ∀ t ∈ Set.Icc (0:ℝ) 1,
      phi p d ((G.ua p) ^ d) + deriv (phi p d) ((G.ua p) ^ d) * (t - (G.ua p) ^ d) ≤ phi p d t :=
    G.support_ua p hp0 hp
  have hconvL : ∀ y ∈ Set.Ioo (0:ℝ) ((G.ua p) ^ d), 0 < phi'' p d y :=
    phi''_pos_left_of_contact hd hp0 hp1 hua0 huas hhua
  have hconvR : ∀ y ∈ Set.Ioo ((G.ub p) ^ d) 1, 0 < phi'' p d y :=
    phi''_pos_right_of_contact hd hp0 hp1 hubs hub1 hhub
  obtain ⟨_, _, hlce⟩ := gc_lce_at_contacts hd G hp0 hp
  -- φ'' > 0 at the contacts
  have huae : Real.rpow ((G.ua p) ^ d) (1/(d:ℝ)) = G.ua p := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hua0.le (by omega)
  have hube : Real.rpow ((G.ub p) ^ d) (1/(d:ℝ)) = G.ub p := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hub0.le (by omega)
  have hφa : 0 < phi'' p d ((G.ua p) ^ d) := by
    rw [phi''_pos_iff hd hxa0, huae]; exact hhua
  have hφb : 0 < phi'' p d ((G.ub p) ^ d) := by
    rw [phi''_pos_iff hd hxb0, hube]; exact hhub
  exact ⟨hxa0, hxa_xb, hxb1, hHxa, hHxb, hchord, hsupp, hconvL, hconvR, hlce, hφa, hφb⟩

/-- Joint continuity of the contact slope `sCM` in `(p,u)` on `(0,1)×(0,1)`. -/
theorem sCM_continuousOn_prod {d : ℕ} (hd : 2 ≤ d) :
    ContinuousOn (fun q : ℝ × ℝ => sCM d q.1 q.2)
      (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) := by
  have hfst : ContinuousOn (fun q : ℝ × ℝ => q.1) (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) :=
    continuous_fst.continuousOn
  have hsnd : ContinuousOn (fun q : ℝ × ℝ => q.2) (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) :=
    continuous_snd.continuousOn
  unfold sCM Jp'
  refine (ContinuousOn.log ?_ ?_).div (continuousOn_const.mul (hsnd.pow (d - 1))) ?_
  · refine (hsnd.mul (continuousOn_const.sub hfst)).div
      ((continuousOn_const.sub hsnd).mul hfst) ?_
    intro q hq; obtain ⟨hp, hu⟩ := Set.mem_prod.mp hq
    exact ne_of_gt (mul_pos (by linarith [hu.2]) hp.1)
  · intro q hq; obtain ⟨hp, hu⟩ := Set.mem_prod.mp hq
    exact ne_of_gt (div_pos (mul_pos hu.1 (by linarith [hp.2])) (mul_pos (by linarith [hu.2]) hp.1))
  · intro q hq; obtain ⟨_, hu⟩ := Set.mem_prod.mp hq
    have hdpos := dpos hd; have := hu.1
    exact ne_of_gt (by positivity)

/-- The supporting line `y ↦ φ_{p,d}(xa) + m (y - xa)` has derivative `m`. -/
private theorem hasDerivAt_supportLine {p : ℝ} {d : ℕ} (xa m y : ℝ) :
    HasDerivAt (fun z => phi p d xa + m * (z - xa)) m y := by
  have := ((hasDerivAt_id y).sub_const xa).const_mul m
  simpa using this.const_add (phi p d xa)

/-- Window quadratic bound for the supporting-line gap at a contact `c`. -/
theorem gap_window_bound {d : ℕ} (hd : 2 ≤ d) {p xa m c η m_K : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hη : 0 < η)
    (hwin : ∀ y ∈ Set.Icc (c - η) (c + η), (0 < y ∧ y < 1) ∧ m_K ≤ phi'' p d y)
    (hfc : phi p d c - (phi p d xa + m * (c - xa)) = 0)
    (hf'c : deriv (phi p d) c = m) :
    ∀ y ∈ Set.Icc (c - η) (c + η),
      m_K / 2 * (y - c) ^ 2 ≤ phi p d y - (phi p d xa + m * (y - xa)) := by
  refine quadratic_lower_of_deriv2_ge (a := c - η) (b := c + η) (c := c) (m := m_K)
    (f := fun y => phi p d y - (phi p d xa + m * (y - xa)))
    (f' := fun y => deriv (phi p d) y - m) (f'' := fun y => phi'' p d y)
    (by linarith) (by linarith) ?_ ?_ ?_ hfc ?_
  · intro y hy
    have hy01 := (hwin y hy).1
    have ha : HasDerivAt (fun y => phi p d xa + m * (y - xa)) m y := hasDerivAt_supportLine xa m y
    have hHy : HasDerivAt (phi p d) (deriv (phi p d) y) y := by
      have h := hasDerivAt_phi hd hp0 hp1 hy01.1 hy01.2; rw [h.deriv]; exact h
    exact hHy.sub ha
  · intro y hy
    have hy01 := (hwin y hy).1
    simpa using (hasDerivAt_phi'' hd hp0 hp1 hy01.1 hy01.2).sub_const m
  · intro y hy; exact (hwin y hy).2
  · show deriv (phi p d) c - m = 0; rw [hf'c]; ring

/-- The gap is antitone on the left convex piece `[0,xa]`. -/
theorem gap_antitone_left {d : ℕ} (hd : 2 ≤ d) {p xa m : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hxa0 : 0 < xa) (hxa1 : xa < 1)
    (hHxa : HasDerivAt (phi p d) m xa)
    (hconvL : ∀ y ∈ Set.Ioo (0:ℝ) xa, 0 < phi'' p d y) :
    AntitoneOn (fun y => phi p d y - (phi p d xa + m * (y - xa))) (Set.Icc 0 xa) := by
  have hconvex : ConvexOn ℝ (Set.Icc 0 xa) (phi p d) :=
    (strictConvexOn_phi_left hd hp0 hp1 hxa0 hxa1 hconvL).convexOn
  have hcont : ContinuousOn (fun y => phi p d y - (phi p d xa + m * (y - xa))) (Set.Icc 0 xa) := by
    refine ((phi_continuousOn_Icc hd hp0 hp1).mono (Set.Icc_subset_Icc le_rfl hxa1.le)).sub ?_
    exact continuousOn_const.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 xa) hcont
  · rw [interior_Icc]; intro y hy
    have hy0 : 0 < y := hy.1
    have ha : HasDerivAt (fun y => phi p d xa + m * (y - xa)) m y := hasDerivAt_supportLine xa m y
    exact ((hasDerivAt_phi hd hp0 hp1 hy0 (lt_trans hy.2 hxa1)).sub ha).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro y hy
    have hy0 : 0 < y := hy.1
    have hyIcc : y ∈ Set.Icc (0:ℝ) xa := ⟨hy.1.le, hy.2.le⟩
    have hxaIcc : xa ∈ Set.Icc (0:ℝ) xa := ⟨hxa0.le, le_refl xa⟩
    have ha : HasDerivAt (fun y => phi p d xa + m * (y - xa)) m y := hasDerivAt_supportLine xa m y
    have hHy : HasDerivAt (phi p d) (deriv (phi p d) y) y := by
      have h := hasDerivAt_phi hd hp0 hp1 hy0 (lt_trans hy.2 hxa1); rw [h.deriv]; exact h
    have hg : HasDerivAt (fun y => phi p d y - (phi p d xa + m * (y - xa)))
        (deriv (phi p d) y - m) y := hHy.sub ha
    rw [hg.deriv]
    have h1 := hconvex.le_slope_of_hasDerivAt hyIcc hxaIcc hy.2 hHy
    have h2 := hconvex.slope_le_of_hasDerivAt hyIcc hxaIcc hy.2 hHxa
    have : deriv (phi p d) y ≤ m := le_trans h1 h2
    linarith

/-- The gap is monotone on the right convex piece `[xb,1]`. -/
theorem gap_monotone_right {d : ℕ} (hd : 2 ≤ d) {p xa m xb : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hxb0 : 0 < xb) (hxb1 : xb < 1)
    (hHxb : HasDerivAt (phi p d) m xb)
    (hconvR : ∀ y ∈ Set.Ioo xb 1, 0 < phi'' p d y) :
    MonotoneOn (fun y => phi p d y - (phi p d xa + m * (y - xa))) (Set.Icc xb 1) := by
  have hconvex : ConvexOn ℝ (Set.Icc xb 1) (phi p d) :=
    (strictConvexOn_phi_right hd hp0 hp1 hxb0 hxb1 hconvR).convexOn
  have hcont : ContinuousOn (fun y => phi p d y - (phi p d xa + m * (y - xa))) (Set.Icc xb 1) := by
    refine ((phi_continuousOn_Icc hd hp0 hp1).mono (Set.Icc_subset_Icc hxb0.le le_rfl)).sub ?_
    exact continuousOn_const.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  apply monotoneOn_of_deriv_nonneg (convex_Icc xb 1) hcont
  · rw [interior_Icc]; intro y hy
    have hy1 : y < 1 := hy.2
    have ha : HasDerivAt (fun y => phi p d xa + m * (y - xa)) m y := hasDerivAt_supportLine xa m y
    exact ((hasDerivAt_phi hd hp0 hp1 (lt_trans hxb0 hy.1) hy1).sub ha).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro y hy
    have hy1 : y < 1 := hy.2
    have hyIcc : y ∈ Set.Icc xb 1 := ⟨hy.1.le, hy.2.le⟩
    have hxbIcc : xb ∈ Set.Icc xb 1 := ⟨le_refl xb, hxb1.le⟩
    have ha : HasDerivAt (fun y => phi p d xa + m * (y - xa)) m y := hasDerivAt_supportLine xa m y
    have hHy : HasDerivAt (phi p d) (deriv (phi p d) y) y := by
      have h := hasDerivAt_phi hd hp0 hp1 (lt_trans hxb0 hy.1) hy1; rw [h.deriv]; exact h
    have hg : HasDerivAt (fun y => phi p d y - (phi p d xa + m * (y - xa)))
        (deriv (phi p d) y - m) y := hHy.sub ha
    rw [hg.deriv]
    have h1 := hconvex.le_slope_of_hasDerivAt hxbIcc hyIcc hy.1 hHxb
    have h2 := hconvex.slope_le_of_hasDerivAt hxbIcc hyIcc hy.1 hHy
    have : m ≤ deriv (phi p d) y := le_trans h1 h2
    linarith

/-- **The per-`r` quadratic separation** (abstract).  Combines the window quadratic
bounds, the convex-piece monotonicity, and the middle lower bound into the uniform
estimate `γ·dist(x,{xa,xb})² ≤ g(x)` on `[0,1]`. -/
theorem quadSep_pointwise {d : ℕ} (hd : 2 ≤ d) {p xa xb m η m_K b_mid x γ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hxa0 : 0 < xa) (hxa_xb : xa < xb) (hxb1 : xb < 1)
    (hHxa : HasDerivAt (phi p d) m xa) (hHxb : HasDerivAt (phi p d) m xb)
    (hchord : phi p d xb = phi p d xa + m * (xb - xa))
    (hconvL : ∀ y ∈ Set.Ioo (0:ℝ) xa, 0 < phi'' p d y)
    (hconvR : ∀ y ∈ Set.Ioo xb 1, 0 < phi'' p d y)
    (hη0 : 0 < η) (hgap : 3 * η ≤ xb - xa)
    (hwinA : ∀ y ∈ Set.Icc (xa - η) (xa + η), (0 < y ∧ y < 1) ∧ m_K ≤ phi'' p d y)
    (hwinB : ∀ y ∈ Set.Icc (xb - η) (xb + η), (0 < y ∧ y < 1) ∧ m_K ≤ phi'' p d y)
    (hmK0 : 0 < m_K)
    (hmid : ∀ y, xa + η ≤ y → y ≤ xb - η → b_mid ≤ phi p d y - (phi p d xa + m * (y - xa)))
    (hγ : γ ≤ m_K / 2 * η ^ 2) (hγ2 : γ ≤ b_mid) (hγ0 : 0 ≤ γ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    γ * (min |x - xa| |x - xb|) ^ 2 ≤ phi p d x - (phi p d xa + m * (x - xa)) := by
  have hxb0 : 0 < xb := lt_trans hxa0 hxa_xb
  have hxa1 : xa < 1 := lt_trans hxa_xb hxb1
  have hmK2 : (0:ℝ) ≤ m_K / 2 := by positivity
  have hη1 : η < 1 := by nlinarith [hgap, hxb1, hxa0]
  have hη2 : η ^ 2 ≤ 1 := by nlinarith [hη0, hη1]
  have hγ_half : γ ≤ m_K / 2 := by nlinarith [hγ, hη2, hmK2]
  have hwa := gap_window_bound hd hp0 hp1 hη0 hwinA (by ring) hHxa.deriv
  have hwb := gap_window_bound hd hp0 hp1 hη0 hwinB (by linarith [hchord]) hHxb.deriv
  have hanti := gap_antitone_left hd hp0 hp1 hxa0 hxa1 hHxa hconvL
  have hmono := gap_monotone_right (xa := xa) hd hp0 hp1 hxb0 hxb1 hHxb hconvR
  have hdist1 : min |x - xa| |x - xb| ≤ |x - xa| := min_le_left _ _
  have hdist2 : min |x - xa| |x - xb| ≤ |x - xb| := min_le_right _ _
  have hdist_nn : 0 ≤ min |x - xa| |x - xb| := le_min (abs_nonneg _) (abs_nonneg _)
  have hdist_le1 : min |x - xa| |x - xb| ≤ 1 := by
    refine le_trans hdist1 ?_; rw [abs_le]; constructor <;> linarith
  have hdistsq1 : (min |x - xa| |x - xb|) ^ 2 ≤ 1 := by nlinarith [hdist_nn, hdist_le1]
  by_cases hcA : |x - xa| ≤ η
  · -- window around `xa`
    have hxw : x ∈ Set.Icc (xa - η) (xa + η) := by
      have h := abs_le.mp hcA; exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hb := hwa x hxw
    have hd2 : (min |x - xa| |x - xb|) ^ 2 ≤ (x - xa) ^ 2 := by
      rw [← sq_abs (x - xa)]; exact pow_le_pow_left₀ hdist_nn hdist1 2
    have t1 : γ * (min |x - xa| |x - xb|) ^ 2 ≤ γ * (x - xa) ^ 2 :=
      mul_le_mul_of_nonneg_left hd2 hγ0
    have t2 : γ * (x - xa) ^ 2 ≤ m_K / 2 * (x - xa) ^ 2 :=
      mul_le_mul_of_nonneg_right hγ_half (sq_nonneg _)
    linarith [t1, t2, hb]
  · replace hcA : η < |x - xa| := not_le.mp hcA
    by_cases hcB : |x - xb| ≤ η
    · -- window around `xb`
      have hxw : x ∈ Set.Icc (xb - η) (xb + η) := by
        have h := abs_le.mp hcB; exact ⟨by linarith [h.1], by linarith [h.2]⟩
      have hb := hwb x hxw
      have hd2 : (min |x - xa| |x - xb|) ^ 2 ≤ (x - xb) ^ 2 := by
        rw [← sq_abs (x - xb)]; exact pow_le_pow_left₀ hdist_nn hdist2 2
      have t1 : γ * (min |x - xa| |x - xb|) ^ 2 ≤ γ * (x - xb) ^ 2 :=
        mul_le_mul_of_nonneg_left hd2 hγ0
      have t2 : γ * (x - xb) ^ 2 ≤ m_K / 2 * (x - xb) ^ 2 :=
        mul_le_mul_of_nonneg_right hγ_half (sq_nonneg _)
      linarith [t1, t2, hb]
    · replace hcB : η < |x - xb| := not_le.mp hcB
      -- away from both contacts: `g(x) ≥ γ`
      have hgx : γ ≤ phi p d x - (phi p d xa + m * (x - xa)) := by
        by_cases hL : x ≤ xa
        · -- left endpoint `x < xa - η`
          have hxlt : x < xa - η := by
            have h := hcA; rw [abs_of_nonpos (by linarith : x - xa ≤ 0)] at h; linarith
          have hax := hanti (a := x) ⟨hx0, by linarith⟩ (b := xa - η) ⟨by linarith, by linarith⟩
            (by linarith)
          have hwe := hwa (xa - η) ⟨le_refl _, by linarith⟩
          have he : ((xa - η) - xa) ^ 2 = η ^ 2 := by ring
          rw [he] at hwe
          linarith [hax, hwe, hγ]
        · replace hL : xa < x := not_le.mp hL
          by_cases hM : x ≤ xb
          · -- middle `xa + η < x < xb - η`
            have hxm1 : xa + η < x := by
              have h := hcA; rw [abs_of_pos (by linarith : 0 < x - xa)] at h; linarith
            have hxm2 : x < xb - η := by
              have h := hcB; rw [abs_of_nonpos (by linarith : x - xb ≤ 0)] at h; linarith
            linarith [hmid x (by linarith) (by linarith), hγ2]
          · replace hM : xb < x := not_le.mp hM
            -- right endpoint `x > xb + η`
            have hxgt : xb + η < x := by
              have h := hcB; rw [abs_of_pos (by linarith : 0 < x - xb)] at h; linarith
            have hmx := hmono (a := xb + η) ⟨by linarith, by linarith⟩ (b := x) ⟨by linarith, hx1⟩
              (by linarith)
            have hwe := hwb (xb + η) ⟨by linarith, le_refl _⟩
            have he : ((xb + η) - xb) ^ 2 = η ^ 2 := by ring
            rw [he] at hwe
            linarith [hmx, hwe, hγ]
      have t : γ * (min |x - xa| |x - xb|) ^ 2 ≤ γ * 1 :=
        mul_le_mul_of_nonneg_left hdistsq1 hγ0
      rw [mul_one] at t; linarith [t, hgx]

/-- **The `quadSep` field: uniform quadratic separation** for an `ArcMaps`.  Condition
(M5) of `thm:scalar-lz-boundary`): on a
compact subarc `K`, the zeros `u_±(p_r)` of `h_{p_r,d}` give, uniformly, two
strictly-convex windows around the contacts `x_a(p_r), x_b(p_r) = {r^d, sm(r)^d}`;
Taylor's theorem with `φ'' ≥ m_K > 0` there (`quadratic_lower_of_deriv2_ge`) yields the
quadratic bound near the contacts, and compactness gives a positive lower bound on the
complement. -/
theorem arcMaps_quadSep {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ} (A : ArcMaps d r₀) :
    ∀ K ⊆ A.U, IsCompact K → ∃ γ : ℝ, 0 < γ ∧ ∀ r ∈ K, ∀ u ∈ Set.Icc (0:ℝ) 1,
      γ * (min |u ^ d - r ^ d| |u ^ d - (A.sm r) ^ d|) ^ 2
        ≤ Jp (A.pc r) u - (Jp (A.pc r) r + slope d A.pc r * (u ^ d - r ^ d)) := by
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, ?_⟩; rw [hKe]; intro r hr; simp at hr
  have hps1 : pStar d < 1 := pStar_lt_one hd
  -- continuous functions on K
  have hpc_cont : ContinuousOn A.pc K := A.analytic_pc.continuousOn.mono hKU
  have hpc_mem : ∀ r ∈ K, A.pc r ∈ Set.Ioo (0:ℝ) (pStar d) := fun r hr => (A.family r (hKU hr)).1
  have hpc_maps : Set.MapsTo A.pc K (Set.Ioo (0:ℝ) (pStar d)) := hpc_mem
  have hpc_mem01 : ∀ r ∈ K, A.pc r ∈ Set.Ioo (0:ℝ) 1 :=
    fun r hr => ⟨(hpc_mem r hr).1, lt_trans (hpc_mem r hr).2 hps1⟩
  have hpc_maps01 : Set.MapsTo A.pc K (Set.Ioo (0:ℝ) 1) := hpc_mem01
  -- contact bundle
  have hbundle := fun r (hr : r ∈ K) => contact_bundle hd A.gc (hpc_mem r hr).1 (hpc_mem r hr).2
  -- xa, xb continuous on K
  have hua_cont : ContinuousOn (fun r => A.gc.ua (A.pc r)) K :=
    (A.gc.continuousOn_ua.mono (Set.Ioo_subset_Ioo le_rfl le_rfl)).comp hpc_cont hpc_maps
  have hub_cont : ContinuousOn (fun r => A.gc.ub (A.pc r)) K :=
    A.gc.continuousOn_ub.comp hpc_cont hpc_maps
  have hxa_cont : ContinuousOn (fun r => (A.gc.ua (A.pc r)) ^ d) K := hua_cont.pow d
  have hxb_cont : ContinuousOn (fun r => (A.gc.ub (A.pc r)) ^ d) K := hub_cont.pow d
  have hxa_mem : ∀ r ∈ K, (A.gc.ua (A.pc r)) ^ d ∈ Set.Ioo (0:ℝ) 1 := by
    intro r hr; obtain ⟨h1, h2, h3, _⟩ := hbundle r hr; exact ⟨h1, lt_trans h2 h3⟩
  have hxb_mem : ∀ r ∈ K, (A.gc.ub (A.pc r)) ^ d ∈ Set.Ioo (0:ℝ) 1 := by
    intro r hr; obtain ⟨h1, h2, h3, _⟩ := hbundle r hr; exact ⟨lt_trans h1 h2, h3⟩
  have hφa_pos : ∀ r ∈ K, 0 < phi'' (A.pc r) d ((A.gc.ua (A.pc r)) ^ d) := by
    intro r hr; obtain ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩ := hbundle r hr; exact h
  have hφb_pos : ∀ r ∈ K, 0 < phi'' (A.pc r) d ((A.gc.ub (A.pc r)) ^ d) := by
    intro r hr; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩ := hbundle r hr; exact h
  -- tube applications
  obtain ⟨η1, m1, hη1, hm1, hwin1⟩ :=
    uniform_phi''_window hd hK hKne hpc_cont hxa_cont hpc_mem01 hxa_mem hφa_pos
  obtain ⟨η2, m2, hη2, hm2, hwin2⟩ :=
    uniform_phi''_window hd hK hKne hpc_cont hxb_cont hpc_mem01 hxb_mem hφb_pos
  -- uniform gap between the contacts
  have hgap_cont : ContinuousOn
      (fun r => (A.gc.ub (A.pc r)) ^ d - (A.gc.ua (A.pc r)) ^ d) K := hxb_cont.sub hxa_cont
  have hgap_pos : ∀ r ∈ K, 0 < (A.gc.ub (A.pc r)) ^ d - (A.gc.ua (A.pc r)) ^ d := by
    intro r hr; obtain ⟨_, h2, _⟩ := hbundle r hr; linarith
  obtain ⟨g0, hg0_pos, hg0_le⟩ := hK.exists_forall_le' hgap_cont hgap_pos
  set η := min η1 (min η2 (g0/3)) with hηdef
  have hη0 : 0 < η := lt_min hη1 (lt_min hη2 (by linarith))
  set m_K := min m1 m2 with hmKdef
  have hmK0 : 0 < m_K := lt_min hm1 hm2
  -- continuity of the slope `m(r)` and `φ(pc r)(xa r)`
  have hm_cont : ContinuousOn (fun r => deriv (phi (A.pc r) d) ((A.gc.ua (A.pc r)) ^ d)) K := by
    have heq : Set.EqOn (fun r => deriv (phi (A.pc r) d) ((A.gc.ua (A.pc r)) ^ d))
        (fun r => sCM d (A.pc r) (A.gc.ua (A.pc r))) K := by
      intro r hr
      have h1 := (hpc_mem r hr).1; have h2 := (hpc_mem r hr).2; have hp1 := lt_trans h2 hps1
      obtain ⟨hua0, huas, _, _, _, _, _⟩ := A.gc.contact (A.pc r) h1 h2
      exact deriv_phi_pow_eq_sCM hd h1 hp1 hua0 (lt_trans huas (rStar_lt_one hd))
    have hmaps : Set.MapsTo (fun r => (A.pc r, A.gc.ua (A.pc r))) K
        (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) := by
      intro r hr
      obtain ⟨hua0, huas, _, _, _, _, _⟩ := A.gc.contact (A.pc r) (hpc_mem r hr).1 (hpc_mem r hr).2
      exact Set.mem_prod.mpr ⟨hpc_mem01 r hr, ⟨hua0, lt_trans huas (rStar_lt_one hd)⟩⟩
    exact ((sCM_continuousOn_prod hd).comp (hpc_cont.prodMk hua_cont) hmaps).congr heq
  have hφxa_cont : ContinuousOn (fun r => phi (A.pc r) d ((A.gc.ua (A.pc r)) ^ d)) K := by
    have hmaps : Set.MapsTo (fun r => (A.pc r, (A.gc.ua (A.pc r)) ^ d)) K
        (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) :=
      fun r hr => Set.mem_prod.mpr ⟨hpc_mem01 r hr, hxa_mem r hr⟩
    exact (phi_continuousOn_prod hd).comp (hpc_cont.prodMk hxa_cont) hmaps
  -- Stage 3: middle compact min via the parametrisation `x = xa + η + t·(xb - xa - 2η)`
  set Kt := K ×ˢ Set.Icc (0:ℝ) 1 with hKtdef
  have hKt : IsCompact Kt := hK.prod isCompact_Icc
  have hfstmaps : Set.MapsTo (Prod.fst : ℝ × ℝ → ℝ) Kt K := fun q hq => (Set.mem_prod.mp hq).1
  have hη_le3 : η ≤ g0 / 3 := le_trans (min_le_right _ _) (min_le_right _ _)
  set xfun : ℝ × ℝ → ℝ :=
    fun q => (A.gc.ua (A.pc q.1)) ^ d + η
      + q.2 * ((A.gc.ub (A.pc q.1)) ^ d - (A.gc.ua (A.pc q.1)) ^ d - 2 * η) with hxfundef
  have hxa_fst : ContinuousOn (fun q : ℝ × ℝ => (A.gc.ua (A.pc q.1)) ^ d) Kt :=
    hxa_cont.comp continuous_fst.continuousOn hfstmaps
  have hxb_fst : ContinuousOn (fun q : ℝ × ℝ => (A.gc.ub (A.pc q.1)) ^ d) Kt :=
    hxb_cont.comp continuous_fst.continuousOn hfstmaps
  have hxfun_cont : ContinuousOn xfun Kt :=
    (hxa_fst.add continuousOn_const).add
      (continuous_snd.continuousOn.mul ((hxb_fst.sub hxa_fst).sub continuousOn_const))
  -- `xfun q ∈ (xa, xb) ⊂ (0,1)`
  have hxfun_lo : ∀ q ∈ Kt, (A.gc.ua (A.pc q.1)) ^ d + η ≤ xfun q := by
    intro q hq; obtain ⟨hqK, hqt⟩ := Set.mem_prod.mp hq
    rw [hxfundef]
    have hgap := hg0_le q.1 hqK
    have hcoef : 0 ≤ (A.gc.ub (A.pc q.1)) ^ d - (A.gc.ua (A.pc q.1)) ^ d - 2 * η := by linarith
    have : 0 ≤ q.2 * ((A.gc.ub (A.pc q.1)) ^ d - (A.gc.ua (A.pc q.1)) ^ d - 2 * η) :=
      mul_nonneg hqt.1 hcoef
    simp only; linarith
  have hxfun_hi : ∀ q ∈ Kt, xfun q ≤ (A.gc.ub (A.pc q.1)) ^ d - η := by
    intro q hq; obtain ⟨hqK, hqt⟩ := Set.mem_prod.mp hq
    rw [hxfundef]
    have hgap := hg0_le q.1 hqK
    have hcoef : 0 ≤ (A.gc.ub (A.pc q.1)) ^ d - (A.gc.ua (A.pc q.1)) ^ d - 2 * η := by linarith
    have : q.2 * ((A.gc.ub (A.pc q.1)) ^ d - (A.gc.ua (A.pc q.1)) ^ d - 2 * η)
        ≤ 1 * ((A.gc.ub (A.pc q.1)) ^ d - (A.gc.ua (A.pc q.1)) ^ d - 2 * η) :=
      mul_le_mul_of_nonneg_right hqt.2 hcoef
    simp only; nlinarith [this]
  have hxfun_mem : ∀ q ∈ Kt, xfun q ∈ Set.Ioo (0:ℝ) 1 := by
    intro q hq; obtain ⟨hqK, _⟩ := Set.mem_prod.mp hq
    have hlo := hxfun_lo q hq; have hhi := hxfun_hi q hq
    obtain ⟨h1, h2, h3, _⟩ := hbundle q.1 hqK
    refine ⟨by linarith, by linarith⟩
  -- the gap evaluated along `xfun`, continuous on `Kt`
  set G : ℝ × ℝ → ℝ :=
    fun q => phi (A.pc q.1) d (xfun q)
      - (phi (A.pc q.1) d ((A.gc.ua (A.pc q.1)) ^ d)
        + deriv (phi (A.pc q.1) d) ((A.gc.ua (A.pc q.1)) ^ d) * (xfun q - (A.gc.ua (A.pc q.1)) ^ d))
    with hGdef
  have hpc_fst : ContinuousOn (fun q : ℝ × ℝ => A.pc q.1) Kt :=
    hpc_cont.comp continuous_fst.continuousOn hfstmaps
  have hphi_joint : ContinuousOn (fun q : ℝ × ℝ => phi (A.pc q.1) d (xfun q)) Kt := by
    have hmaps : Set.MapsTo (fun q : ℝ × ℝ => (A.pc q.1, xfun q)) Kt
        (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) :=
      fun q hq => Set.mem_prod.mpr ⟨hpc_mem01 q.1 (hfstmaps hq), hxfun_mem q hq⟩
    exact (phi_continuousOn_prod hd).comp (hpc_fst.prodMk hxfun_cont) hmaps
  have hG_cont : ContinuousOn G Kt := by
    refine hphi_joint.sub ((hφxa_cont.comp continuous_fst.continuousOn hfstmaps).add ?_)
    exact (hm_cont.comp continuous_fst.continuousOn hfstmaps).mul (hxfun_cont.sub hxa_fst)
  have hG_pos : ∀ q ∈ Kt, 0 < G q := by
    intro q hq
    obtain ⟨hqK, _⟩ := Set.mem_prod.mp hq
    have h1 := (hpc_mem q.1 hqK).1; have h2 := (hpc_mem q.1 hqK).2; have hp1 := lt_trans h2 hps1
    obtain ⟨hxa0, hxa_xb, hxb1, hHxa, hHxb, hchord, hsupp, hconvL, hconvR, hlce, _, _⟩ :=
      hbundle q.1 hqK
    have hlo := hxfun_lo q hq; have hhi := hxfun_hi q hq
    have hxmem : xfun q ∈ Set.Icc (0:ℝ) 1 := ⟨(hxfun_mem q hq).1.le, (hxfun_mem q hq).2.le⟩
    have hne1 : xfun q ≠ (A.gc.ua (A.pc q.1)) ^ d := by
      have : (A.gc.ua (A.pc q.1)) ^ d < xfun q := by linarith
      exact ne_of_gt this
    have hne2 : xfun q ≠ (A.gc.ub (A.pc q.1)) ^ d := by
      have : xfun q < (A.gc.ub (A.pc q.1)) ^ d := by linarith
      exact ne_of_lt this
    exact gap_pos_abstract hd h1 hp1 hxa0 hxa_xb hxb1 hHxa hHxb hchord hsupp hconvL hconvR hlce
      hxmem.1 hxmem.2 hne1 hne2
  obtain ⟨b_mid, hb_pos, hb_le⟩ := hKt.exists_forall_le' hG_cont hG_pos
  -- Stage 4–5: the uniform constant and the per-`r` bound
  refine ⟨min (m_K / 2 * η ^ 2) b_mid, lt_min (by positivity) hb_pos, ?_⟩
  intro r hr u hu
  have hr_U := hKU hr
  obtain ⟨hpc_io, hfamily_r⟩ := A.family r hr_U
  have hp0 : 0 < A.pc r := hpc_io.1
  have hp_ps : A.pc r < pStar d := hpc_io.2
  have hp1 : A.pc r < 1 := lt_trans hp_ps hps1
  obtain ⟨hr0', hpcr, hr1, _, _, _⟩ := A.ordering r hr_U
  have hr0 : 0 < r := lt_trans hp0 hpcr
  obtain ⟨hxa0, hxa_xb, hxb1, hHxa, hHxb, hchord, _, hconvL, hconvR, hlce, _, _⟩ := hbundle r hr
  have hx0 : (0:ℝ) ≤ u ^ d := pow_nonneg hu.1 d
  have hx1 : u ^ d ≤ 1 := pow_le_one₀ hu.1 hu.2
  have hden : 0 < (A.gc.ub (A.pc r)) ^ d - (A.gc.ua (A.pc r)) ^ d - 2 * η := by
    have h := hg0_le r hr; have := hη_le3; linarith
  have hgap_r : 3 * η ≤ (A.gc.ub (A.pc r)) ^ d - (A.gc.ua (A.pc r)) ^ d := by
    have h := hg0_le r hr; have := hη_le3; linarith
  have hwinA_r : ∀ y ∈ Set.Icc ((A.gc.ua (A.pc r)) ^ d - η) ((A.gc.ua (A.pc r)) ^ d + η),
      (0 < y ∧ y < 1) ∧ m_K ≤ phi'' (A.pc r) d y := by
    intro y hy
    have hηη1 : η ≤ η1 := min_le_left _ _
    have hy1 : y ∈ Set.Icc ((A.gc.ua (A.pc r)) ^ d - η1) ((A.gc.ua (A.pc r)) ^ d + η1) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact ⟨(hwin1 r hr y hy1).1, le_trans (min_le_left m1 m2) (hwin1 r hr y hy1).2⟩
  have hwinB_r : ∀ y ∈ Set.Icc ((A.gc.ub (A.pc r)) ^ d - η) ((A.gc.ub (A.pc r)) ^ d + η),
      (0 < y ∧ y < 1) ∧ m_K ≤ phi'' (A.pc r) d y := by
    intro y hy
    have hηη2 : η ≤ η2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hy1 : y ∈ Set.Icc ((A.gc.ub (A.pc r)) ^ d - η2) ((A.gc.ub (A.pc r)) ^ d + η2) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact ⟨(hwin2 r hr y hy1).1, le_trans (min_le_right m1 m2) (hwin2 r hr y hy1).2⟩
  have hmid_r : ∀ y, (A.gc.ua (A.pc r)) ^ d + η ≤ y → y ≤ (A.gc.ub (A.pc r)) ^ d - η →
      b_mid ≤ phi (A.pc r) d y
        - (phi (A.pc r) d ((A.gc.ua (A.pc r)) ^ d)
          + deriv (phi (A.pc r) d) ((A.gc.ua (A.pc r)) ^ d) * (y - (A.gc.ua (A.pc r)) ^ d)) := by
    intro y hy1 hy2
    set t := (y - (A.gc.ua (A.pc r)) ^ d - η)
      / ((A.gc.ub (A.pc r)) ^ d - (A.gc.ua (A.pc r)) ^ d - 2 * η) with htdef
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
    have ht1 : t ≤ 1 := by rw [div_le_one hden]; linarith
    have hxe : xfun (r, t) = y := by
      have hne := ne_of_gt hden
      show (A.gc.ua (A.pc r)) ^ d + η
        + t * ((A.gc.ub (A.pc r)) ^ d - (A.gc.ua (A.pc r)) ^ d - 2 * η) = y
      rw [htdef, div_mul_cancel₀ _ hne]; ring
    have hmem : (r, t) ∈ Kt := Set.mem_prod.mpr ⟨hr, ⟨ht0, ht1⟩⟩
    have hb := hb_le (r, t) hmem
    rw [hGdef] at hb; simp only at hb; rw [hxe] at hb; exact hb
  have hmain := quadSep_pointwise hd hp0 hp1 hxa0 hxa_xb hxb1 hHxa hHxb hchord hconvL hconvR
    hη0 hgap_r hwinA_r hwinB_r hmK0 hmid_r (min_le_left _ _) (min_le_right _ _)
    (le_of_lt (lt_min (by positivity) hb_pos)) hx0 hx1
  -- convert to the statement
  have hJu : Jp (A.pc r) u = phi (A.pc r) d (u ^ d) := Jp_eq_phi_pow hd hu.1
  have hJr : Jp (A.pc r) r = phi (A.pc r) d (r ^ d) := Jp_eq_phi_pow hd hr0.le
  have hsl : slope d A.pc r = deriv (phi (A.pc r) d) (r ^ d) :=
    slope_eq_deriv_phi hd hp0 hp1 hr0 hr1
  rw [hJu, hJr, hsl]
  rcases hfamily_r with ⟨hrlt, hua_eq, hsm_eq⟩ | ⟨hrgt, hub_eq, hsm_eq⟩
  · -- lower family: `r^d = xa`, `sm^d = xb`
    rw [hua_eq, ← hsm_eq] at hmain
    exact hmain
  · -- upper family: `r^d = xb`, `sm^d = xa`
    have hxbr : (A.gc.ub (A.pc r)) ^ d = r ^ d := by rw [hub_eq]
    have hLineU : phi (A.pc r) d (r ^ d) + deriv (phi (A.pc r) d) (r ^ d) * (u ^ d - r ^ d)
        = phi (A.pc r) d ((A.gc.ua (A.pc r)) ^ d)
          + deriv (phi (A.pc r) d) ((A.gc.ua (A.pc r)) ^ d) * (u ^ d - (A.gc.ua (A.pc r)) ^ d) := by
      rw [← hxbr, hHxb.deriv, hchord]; ring
    have hmin_eq : min |u ^ d - r ^ d| |u ^ d - (A.sm r) ^ d|
        = min |u ^ d - (A.gc.ua (A.pc r)) ^ d| |u ^ d - (A.gc.ub (A.pc r)) ^ d| := by
      rw [hsm_eq, ← hxbr, min_comm]
    rw [hLineU, hmin_eq]; exact hmain

/-- **The `orientation` field** for an `ArcMaps`.  The replica-symmetric half of
condition (M2) of `thm:scalar-lz-boundary`: by the contact
monotonicity (`dx_a/dp > 0` on the lower family, `dx_b/dp < 0` on the upper), for
`p > pc(r)` the relevant contact moves so that `r^d` sits on a strictly convex piece
of the convex minorant (a supporting line at `r^d` persists), while for `p < pc(r)`
the point `r^d` falls strictly between the two contacts (inside the affine segment),
where no supporting line at `r^d` lies below `φ_{p,d}`. -/
theorem arcMaps_orientation {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ} (A : ArcMaps d r₀) :
    ∀ r ∈ A.U, ∀ p, A.pc r < p → p < pStar d →
      ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x := by
  intro r hr p hp_gt hp_ps
  have hps1 : pStar d < 1 := pStar_lt_one hd
  have hus0 : 0 < rStar d := rStar_pos hd
  have hus1 : rStar d < 1 := rStar_lt_one hd
  obtain ⟨hpc_io, hfamily⟩ := A.family r hr
  obtain ⟨_, hpcr, hr1, _, _, _⟩ := A.ordering r hr
  have hp₀0 : 0 < A.pc r := hpc_io.1
  have hp₀ps : A.pc r < pStar d := hpc_io.2
  have hr0 : 0 < r := lt_trans hp₀0 hpcr
  have hp₀mem : A.pc r ∈ Set.Ioo (0:ℝ) (pStar d) := ⟨hp₀0, hp₀ps⟩
  have hp0 : 0 < p := lt_trans hp₀0 hp_gt
  have hp1 : p < 1 := lt_trans hp_ps hps1
  have hpmem : p ∈ Set.Ioo (0:ℝ) (pStar d) := ⟨hp0, hp_ps⟩
  refine ⟨deriv (phi p d) (r ^ d), fun x hx => ?_⟩
  rw [Jp_eq_phi_pow hd hr0.le]
  rcases hfamily with ⟨hrlt, hua_eq, _⟩ | ⟨hrgt, hub_eq, _⟩
  · -- lower family: `r^d < (u_a p)^d`, left convex piece
    obtain ⟨hua0, huas, _, _, _, hhua, _⟩ := A.gc.contact p hp0 hp_ps
    have hr_lt_ua : r < A.gc.ua p := by
      have h := A.gc.mono_ua hp₀mem hpmem hp_gt; rwa [hua_eq] at h
    have hrd_lt : r ^ d < (A.gc.ua p) ^ d := pow_lt_pow_left₀ hr_lt_ua hr0.le (by omega)
    have hc1 : (A.gc.ua p) ^ d < 1 := pow_lt_one₀ hua0.le (lt_trans huas hus1) (by omega)
    have hconv := phi''_pos_left_of_contact hd hp0 hp1 hua0 huas hhua
    exact supportingLine_left_of_convex hd hp0 hp1 (pow_pos hr0 d) hrd_lt hc1 hconv
      (A.gc.support_ua p hp0 hp_ps) x hx
  · -- upper family: `(u_b p)^d < r^d`, right convex piece
    obtain ⟨_, _, hubs, hub1, _, _, hhub⟩ := A.gc.contact p hp0 hp_ps
    have hub0 : 0 < A.gc.ub p := lt_trans hus0 hubs
    have hub_lt_r : A.gc.ub p < r := by
      have h := A.gc.mono_ub hp₀mem hpmem hp_gt; rwa [hub_eq] at h
    have hrd_gt : (A.gc.ub p) ^ d < r ^ d := pow_lt_pow_left₀ hub_lt_r hub0.le (by omega)
    have hrd1 : r ^ d < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
    have hconv := phi''_pos_right_of_contact hd hp0 hp1 hubs hub1 hhub
    exact supportingLine_right_of_convex hd hp0 hp1 (pow_pos hub0 d) hrd_gt hrd1 hconv
      (A.gc.support_ub p hp0 hp_ps) x hx


/-- **The broken side of the Lubetzky–Zhao boundary, globally** (the `p < pc(r)` half of
condition (M2) of `thm:scalar-lz-boundary`).
For `r` on the arc and *every* `0 < p < pc(r)`, no supporting line lies below `φ_{p,d}` at
`x = r^d`.  This strengthens the negative side of `arcMaps_orientation` from a local
window `(pc r − δ, pc r)` to the full broken side `(0, pc r)`: the only role of `δ` there is
to force `p > 0`, while the geometric input (`r^d` strictly between the contacts, which is
where `gc_lce_at_contacts` puts the convex minorant strictly below `φ`) holds for all
`p ∈ (0, pc r)` by the monotonicity of the contact maps. -/
theorem arcMaps_brokenSide {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ} (A : ArcMaps d r₀) :
    ∀ r ∈ A.U, ∀ p, 0 < p → p < A.pc r →
      ¬ ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x := by
  intro r hr p hp0 hp_lt
  have hps1 : pStar d < 1 := pStar_lt_one hd
  have hus1 : rStar d < 1 := rStar_lt_one hd
  obtain ⟨hpc_io, hfamily⟩ := A.family r hr
  obtain ⟨_, hpcr, hr1, _, _, _⟩ := A.ordering r hr
  have hp₀0 : 0 < A.pc r := hpc_io.1
  have hp₀ps : A.pc r < pStar d := hpc_io.2
  have hr0 : 0 < r := lt_trans hp₀0 hpcr
  have hp₀mem : A.pc r ∈ Set.Ioo (0:ℝ) (pStar d) := ⟨hp₀0, hp₀ps⟩
  have hp_ps : p < pStar d := lt_trans hp_lt hp₀ps
  have hp1 : p < 1 := lt_trans hp_ps hps1
  have hpmem : p ∈ Set.Ioo (0:ℝ) (pStar d) := ⟨hp0, hp_ps⟩
  -- `r^d` is strictly between the two contacts (monotonicity of the contact maps)
  have hrmem : r ^ d ∈ Set.Ioo ((A.gc.ua p) ^ d) ((A.gc.ub p) ^ d) := by
    rcases hfamily with ⟨hrlt, hua_eq, _⟩ | ⟨hrgt, hub_eq, _⟩
    · obtain ⟨hua0, _, hubs, _, _, _, _⟩ := A.gc.contact p hp0 hp_ps
      have hua_lt_r : A.gc.ua p < r := by
        have h := A.gc.mono_ua hpmem hp₀mem hp_lt; rwa [hua_eq] at h
      exact ⟨pow_lt_pow_left₀ hua_lt_r hua0.le (by omega),
        pow_lt_pow_left₀ (lt_trans hrlt hubs) hr0.le (by omega)⟩
    · obtain ⟨hua0, huas, _, _, _, _, _⟩ := A.gc.contact p hp0 hp_ps
      have hr_lt_ub : r < A.gc.ub p := by
        have h := A.gc.mono_ub hpmem hp₀mem hp_lt; rwa [hub_eq] at h
      exact ⟨pow_lt_pow_left₀ (lt_trans huas hrgt) hua0.le (by omega),
        pow_lt_pow_left₀ hr_lt_ub hr0.le (by omega)⟩
  -- there the convex minorant is strictly below `φ`, so no supporting line exists
  rintro ⟨a, ha⟩
  obtain ⟨_, _, hLlt⟩ := gc_lce_at_contacts hd A.gc hp0 hp_ps
  have hlt := hLlt (r ^ d) hrmem
  have hcont := phi_continuousOn_Icc hd hp0 hp1
  have hrIoo : r ^ d ∈ Set.Ioo (0:ℝ) 1 := ⟨pow_pos hr0 d, pow_lt_one₀ hr0.le hr1 (by omega)⟩
  have hiff := exists_supportingLine_iff_lce_eq (show (0:ℝ) < 1 by norm_num) hcont hrIoo
  have hsupp : ∃ s : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, phi p d (r ^ d) + s * (x - r ^ d) ≤ phi p d x :=
    ⟨a, fun x hx => by have h := ha x hx; rwa [Jp_eq_phi_pow hd hr0.le] at h⟩
  have heq := hiff.mp hsupp
  linarith [hlt, heq]

open MeasureTheory in
/-- A probability measure that is a.e. constant equals the Dirac mass there. -/
theorem measure_eq_dirac_of_ae_eq {c : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : ∀ᵐ x ∂μ, x = c) : μ = Measure.dirac c := by
  have hcompl : μ ({c}ᶜ) = 0 := by
    have hc0 : μ {x | x ≠ c} = 0 := by rwa [← ae_iff]
    have hset : ({c}ᶜ : Set ℝ) = {x | x ≠ c} := by ext x; simp
    rw [hset]; exact hc0
  have hmc : μ {c} = 1 := by
    have hadd := measure_add_measure_compl (μ := μ) (measurableSet_singleton c)
    rw [hcompl, add_zero, measure_univ] at hadd; exact hadd
  ext s hs
  by_cases hcs : c ∈ s
  · rw [Measure.dirac_apply_of_mem hcs]
    exact le_antisymm prob_le_one (hmc ▸ measure_mono (Set.singleton_subset_iff.mpr hcs))
  · rw [(dirac_eq_zero_iff_not_mem hs).mpr hcs]
    have hsub : s ⊆ {c}ᶜ := fun x hx hxc => hcs (hxc ▸ hx)
    exact le_antisymm (le_trans (measure_mono hsub) hcompl.le) zero_le

/-- **The strict supporting line at `r^d`** on the whole replica-symmetric window
`pc r < p < p_*`.  Returns the tangent slope `a = φ'_{p,d}(r^d)` with `L ≤ φ_{p,d}`
on `[0,1]` and `L < φ_{p,d}` strictly away from `r^d`.  (M6's geometric input.) -/
theorem m6_supporting_line {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ} (A : ArcMaps d r₀) {r : ℝ}
    (hrU : r ∈ A.U) {p : ℝ} (hp_gt : A.pc r < p) (hp_ps : p < pStar d) :
    ∃ a : ℝ, (∀ x ∈ Set.Icc (0:ℝ) 1, phi p d (r ^ d) + a * (x - r ^ d) ≤ phi p d x) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, x ≠ r ^ d → phi p d (r ^ d) + a * (x - r ^ d) < phi p d x) := by
  have hps1 : pStar d < 1 := pStar_lt_one hd
  have hus0 : 0 < rStar d := rStar_pos hd
  have hus1 : rStar d < 1 := rStar_lt_one hd
  obtain ⟨hpc_io, hfamily⟩ := A.family r hrU
  obtain ⟨_, hpcr, hr1, _, _, _⟩ := A.ordering r hrU
  have hp₀0 : 0 < A.pc r := hpc_io.1
  have hp₀ps : A.pc r < pStar d := hpc_io.2
  have hr0 : 0 < r := lt_trans hp₀0 hpcr
  have hp₀mem : A.pc r ∈ Set.Ioo (0:ℝ) (pStar d) := ⟨hp₀0, hp₀ps⟩
  have hp0 : 0 < p := lt_trans hp₀0 hp_gt
  have hp1 : p < 1 := lt_trans hp_ps hps1
  have hpmem : p ∈ Set.Ioo (0:ℝ) (pStar d) := ⟨hp0, hp_ps⟩
  refine ⟨deriv (phi p d) (r ^ d), ?_, ?_⟩ <;>
  rcases hfamily with ⟨hrlt, hua_eq, _⟩ | ⟨hrgt, hub_eq, _⟩
  · -- ≤, lower family
    obtain ⟨hua0, huas, _, _, _, hhua, _⟩ := A.gc.contact p hp0 hp_ps
    have hr_lt_ua : r < A.gc.ua p := by
      have h := A.gc.mono_ua hp₀mem hpmem hp_gt; rwa [hua_eq] at h
    have hrd_lt : r ^ d < (A.gc.ua p) ^ d := pow_lt_pow_left₀ hr_lt_ua hr0.le (by omega)
    have hc1 : (A.gc.ua p) ^ d < 1 := pow_lt_one₀ hua0.le (lt_trans huas hus1) (by omega)
    exact supportingLine_left_of_convex hd hp0 hp1 (pow_pos hr0 d) hrd_lt hc1
      (phi''_pos_left_of_contact hd hp0 hp1 hua0 huas hhua) (A.gc.support_ua p hp0 hp_ps)
  · -- ≤, upper family
    obtain ⟨_, _, hubs, hub1, _, _, hhub⟩ := A.gc.contact p hp0 hp_ps
    have hub0 : 0 < A.gc.ub p := lt_trans hus0 hubs
    have hub_lt_r : A.gc.ub p < r := by
      have h := A.gc.mono_ub hp₀mem hpmem hp_gt; rwa [hub_eq] at h
    have hrd_gt : (A.gc.ub p) ^ d < r ^ d := pow_lt_pow_left₀ hub_lt_r hub0.le (by omega)
    have hrd1 : r ^ d < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
    exact supportingLine_right_of_convex hd hp0 hp1 (pow_pos hub0 d) hrd_gt hrd1
      (phi''_pos_right_of_contact hd hp0 hp1 hubs hub1 hhub) (A.gc.support_ub p hp0 hp_ps)
  · -- <, lower family
    obtain ⟨hua0, huas, _, _, _, hhua, _⟩ := A.gc.contact p hp0 hp_ps
    have hr_lt_ua : r < A.gc.ua p := by
      have h := A.gc.mono_ua hp₀mem hpmem hp_gt; rwa [hua_eq] at h
    have hrd_lt : r ^ d < (A.gc.ua p) ^ d := pow_lt_pow_left₀ hr_lt_ua hr0.le (by omega)
    have hc1 : (A.gc.ua p) ^ d < 1 := pow_lt_one₀ hua0.le (lt_trans huas hus1) (by omega)
    exact supportingLine_left_of_convex_strict hd hp0 hp1 (pow_pos hr0 d) hrd_lt hc1
      (phi''_pos_left_of_contact hd hp0 hp1 hua0 huas hhua) (A.gc.support_ua p hp0 hp_ps)
  · -- <, upper family
    obtain ⟨_, _, hubs, hub1, _, _, hhub⟩ := A.gc.contact p hp0 hp_ps
    have hub0 : 0 < A.gc.ub p := lt_trans hus0 hubs
    have hub_lt_r : A.gc.ub p < r := by
      have h := A.gc.mono_ub hp₀mem hpmem hp_gt; rwa [hub_eq] at h
    have hrd_gt : (A.gc.ub p) ^ d < r ^ d := pow_lt_pow_left₀ hub_lt_r hub0.le (by omega)
    have hrd1 : r ^ d < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
    exact supportingLine_right_of_convex_strict hd hp0 hp1 (pow_pos hub0 d) hrd_gt hrd1
      (phi''_pos_right_of_contact hd hp0 hp1 hubs hub1 hhub) (A.gc.support_ub p hp0 hp_ps)

open MeasureTheory in
/-- **From a strict supporting line to "no flat tie".**  If the affine function
`L(x) = φ_{p,d}(r^d) + a(x - r^d)` lies below `φ_{p,d}` on `[0,1]`, strictly away from `r^d`,
then every `[0,1]`-valued law `μ` of mean `r^d` satisfies `∫ φ_{p,d} dμ ≥ J_p(r)`, with equality
only for `μ = δ_{r^d}`.  This is the measure-theoretic half of `noFlatTie`, isolated from the
source of the supporting line: `m6_supporting_line` supplies one on the arc's window
`(pc r, p_*)`, and `supportingLine_strict_of_pStar_le` supplies one for every `p ≥ p_*`. -/
theorem noFlatTie_of_strict_supporting {d : ℕ} (hd : 2 ≤ d) {p r a : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hr0 : 0 < r)
    (hLle : ∀ x ∈ Set.Icc (0:ℝ) 1, phi p d (r ^ d) + a * (x - r ^ d) ≤ phi p d x)
    (hLlt : ∀ x ∈ Set.Icc (0:ℝ) 1, x ≠ r ^ d → phi p d (r ^ d) + a * (x - r ^ d) < phi p d x) :
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc (0:ℝ) 1)ᶜ = 0 →
      (∫ x, x ∂μ = r ^ d) →
        Jp p r ≤ ∫ x, phi p d x ∂μ ∧
          (∫ x, phi p d x ∂μ = Jp p r → μ = Measure.dirac (r ^ d)) := by
  intro μ hμ hμcompl hμmean
  have hJr : phi p d (r ^ d) = Jp p r := (Jp_eq_phi_pow hd hr0.le).symm
  -- `μ` lives on `[0,1]`
  have hμae : ∀ᵐ x ∂μ, x ∈ Set.Icc (0:ℝ) 1 := by rw [ae_iff]; exact hμcompl
  have hrestrict : μ.restrict (Set.Icc (0:ℝ) 1) = μ := Measure.restrict_eq_self_of_ae_mem hμae
  -- integrability of `φ_p`, `id`, `L`
  have hint_phi : Integrable (phi p d) μ := by
    rw [← hrestrict]; exact (phi_continuousOn_Icc hd hp0 hp1).integrableOn_Icc
  have hint_id : Integrable (fun x : ℝ => x) μ := by
    rw [← hrestrict]; exact (continuous_id.continuousOn).integrableOn_Icc
  have hint_aff : Integrable (fun x => a * (x - r ^ d)) μ :=
    (hint_id.sub (integrable_const _)).const_mul a
  have hint_L : Integrable (fun x => phi p d (r ^ d) + a * (x - r ^ d)) μ :=
    (integrable_const _).add hint_aff
  -- `∫ L dμ = Jp p r`
  have hintL : ∫ x, (phi p d (r ^ d) + a * (x - r ^ d)) ∂μ = Jp p r := by
    rw [integral_add (integrable_const _) hint_aff, integral_const_mul,
      integral_sub hint_id (integrable_const _), hμmean]
    simp [integral_const, hJr]
  -- `L ≤ φ_p` a.e.
  have hLle_ae : ∀ᵐ x ∂μ, phi p d (r ^ d) + a * (x - r ^ d) ≤ phi p d x := by
    filter_upwards [hμae] with x hx; exact hLle x hx
  refine ⟨?_, ?_⟩
  · -- Jensen inequality
    calc Jp p r = ∫ x, (phi p d (r ^ d) + a * (x - r ^ d)) ∂μ := hintL.symm
      _ ≤ ∫ x, phi p d x ∂μ := integral_mono_ae hint_L hint_phi hLle_ae
  · -- equality ⟹ Dirac
    intro heq
    have hzero : ∫ x, (phi p d x - (phi p d (r ^ d) + a * (x - r ^ d))) ∂μ = 0 := by
      rw [integral_sub hint_phi hint_L, hintL, heq]; ring
    have hnn : 0 ≤ᵐ[μ] fun x => phi p d x - (phi p d (r ^ d) + a * (x - r ^ d)) := by
      filter_upwards [hLle_ae] with x hx
      show (0:ℝ) ≤ phi p d x - (phi p d (r ^ d) + a * (x - r ^ d)); linarith
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae hnn (hint_phi.sub hint_L)).mp hzero
    -- the gap is zero only at `r^d`, so `μ`-a.e. `x = r^d`
    have haeeq : ∀ᵐ x ∂μ, x = r ^ d := by
      filter_upwards [hae0, hμae] with x hx hxmem
      by_contra hne
      have hlt := hLlt x hxmem hne
      have hgap : phi p d x - (phi p d (r ^ d) + a * (x - r ^ d)) = 0 := hx
      linarith
    exact measure_eq_dirac_of_ae_eq haeeq

open MeasureTheory in
/-- **The `noFlatTie` field: no flat tie** (Jensen form) for an `ArcMaps`.  A Lean-side
window condition with no counterpart in `thm:scalar-lz-boundary`: on
the whole replica-symmetric window `pc(r) < p < p_*`, the point `(r^d, J_p(r))`
is not on any nontrivial straight segment of the convex minorant of
`x ↦ J_p(x^{1/d})`; equivalently, any `[0,1]`-valued law of mean `r^d` has
`∫ φ_{p,d} ≥ J_p(r)`, with equality only at the Dirac mass at `r^d`. -/
theorem arcMaps_noFlatTie {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ} (A : ArcMaps d r₀) :
    ∀ r ∈ A.U, ∀ p, A.pc r < p → p < pStar d →
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc (0:ℝ) 1)ᶜ = 0 →
        (∫ x, x ∂μ = r ^ d) →
          Jp p r ≤ ∫ x, phi p d x ∂μ ∧
            (∫ x, phi p d x ∂μ = Jp p r → μ = Measure.dirac (r ^ d)) := by
  intro r hrU p hp_gt hp_ps
  obtain ⟨hpc_io, _⟩ := A.family r hrU
  obtain ⟨_, hpcr, hr1, _, _, _⟩ := A.ordering r hrU
  have hp₀0 : 0 < A.pc r := hpc_io.1
  have hr0 : 0 < r := lt_trans hp₀0 hpcr
  have hp0 : 0 < p := lt_trans hp₀0 hp_gt
  have hp1 : p < 1 := lt_trans hp_ps (pStar_lt_one hd)
  obtain ⟨s, hLle, hLlt⟩ := m6_supporting_line hd A hrU hp_gt hp_ps
  exact noFlatTie_of_strict_supporting hd hp0 hp1 hr0 hLle hLlt

/-! ### Above `p_*`: the same two conclusions from strict convexity

The arc's `orientation` and `noFlatTie` fields are stated on the window `(pc r, p_*)`, because
below `p_*` the function `φ_{p,d}` is not convex and the supporting line has to be produced from
the contact maps.  Above `p_*` there is nothing to produce: `φ_{p,d}` is strictly convex on the
whole of `[0,1]`, so its tangent at `r^d` is a strict supporting line.  These two lemmas are the
`p ≥ p_*` counterparts of the two fields, and let `replica_symmetric_unique` run on the full
range `pc(r) ≤ p < r`. -/

/-- **The strict supporting line at `r^d` above `p_*`.**  For `p_* ≤ p < 1` the function
`φ_{p,d}` is strictly convex on `[0,1]` (`strictConvexOn_phi_of_pStar_le`), so its tangent at the
interior point `r^d` lies below it, strictly away from the contact. -/
theorem supportingLine_strict_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p r : ℝ}
    (hps : pStar d ≤ p) (hp1 : p < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ a : ℝ, (∀ x ∈ Set.Icc (0:ℝ) 1, phi p d (r ^ d) + a * (x - r ^ d) ≤ phi p d x) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, x ≠ r ^ d → phi p d (r ^ d) + a * (x - r ^ d) < phi p d x) := by
  have hp0 : 0 < p := lt_of_lt_of_le (pStar_pos hd) hps
  have hrd0 : 0 < r ^ d := pow_pos hr0 d
  have hrd1 : r ^ d < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hsconv : StrictConvexOn ℝ (Set.Icc 0 1) (phi p d) :=
    strictConvexOn_phi_of_pStar_le hd hps hp1
  have hH : HasDerivAt (phi p d) (deriv (phi p d) (r ^ d)) (r ^ d) := by
    have h := hasDerivAt_phi hd hp0 hp1 hrd0 hrd1; rw [h.deriv]; exact h
  have hmem : r ^ d ∈ Set.Icc (0:ℝ) 1 := ⟨hrd0.le, hrd1.le⟩
  refine ⟨deriv (phi p d) (r ^ d), ?_, strictConvexOn_tangent_lt hsconv hmem hH⟩
  intro x hx
  rcases eq_or_ne x (r ^ d) with rfl | hne
  · simp
  · exact le_of_lt (strictConvexOn_tangent_lt hsconv hmem hH x hx hne)

/-- **The `orientation` conclusion above `p_*`**, in the `J_p` form of the arc field: for
`p_* ≤ p < 1` and `r ∈ (0,1)` a supporting line of `φ_{p,d}` at `x = r^d` exists. -/
theorem orientation_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p r : ℝ}
    (hps : pStar d ≤ p) (hp1 : p < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x := by
  obtain ⟨a, hLle, -⟩ := supportingLine_strict_of_pStar_le hd hps hp1 hr0 hr1
  refine ⟨a, ?_⟩
  rw [Jp_eq_phi_pow hd hr0.le]
  exact hLle

open MeasureTheory in
/-- **The `noFlatTie` conclusion above `p_*`**: for `p_* ≤ p < 1` and `r ∈ (0,1)`, any
`[0,1]`-valued law of mean `r^d` has `∫ φ_{p,d} ≥ J_p(r)`, with equality only at `δ_{r^d}`. -/
theorem noFlatTie_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p r : ℝ}
    (hps : pStar d ≤ p) (hp1 : p < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc (0:ℝ) 1)ᶜ = 0 →
      (∫ x, x ∂μ = r ^ d) →
        Jp p r ≤ ∫ x, phi p d x ∂μ ∧
          (∫ x, phi p d x ∂μ = Jp p r → μ = Measure.dirac (r ^ d)) := by
  obtain ⟨a, hLle, hLlt⟩ := supportingLine_strict_of_pStar_le hd hps hp1 hr0 hr1
  exact noFlatTie_of_strict_supporting hd (lt_of_lt_of_le (pStar_pos hd) hps) hp1 hr0 hLle hLlt

/-- **`thm:scalar-lz-boundary`.**  For every
non-exceptional target density `r₀ ∈ (0,1) \ {(d-1)/d}` there is an oriented
regular Lubetzky–Zhao boundary arc whose interval `U` contains `r₀`, and `r₀` is
non-exceptional for it.

The proof assembles the `LZBoundaryArc` record from the construction data
`exists_arcMaps` (the shallow fields) and the regularity lemmas `arcMaps_quadSep`,
`arcMaps_orientation`, `arcMaps_noFlatTie`; the record assembly and
non-exceptionality are discharged here directly. -/
theorem scalar_lz_boundary_arcs {d : ℕ} (hd : 2 ≤ d) {r₀ : ℝ}
    (hr₀0 : 0 < r₀) (hr₀1 : r₀ < 1) (hexc : r₀ ≠ rStar d) :
    ∃ M : LZBoundaryArc d, r₀ ∈ M.U ∧ M.NonExceptional r₀ := by
  obtain ⟨A⟩ := exists_arcMaps hd hr₀0 hr₀1 hexc
  refine ⟨{ U := A.U, isOpen_U := A.isOpen_U, pc := A.pc, sm := A.sm,
            analytic_pc := A.analytic_pc, analytic_sm := A.analytic_sm,
            ordering := A.ordering, supporting := A.supporting,
            secondContact := A.secondContact,
            quadSep := arcMaps_quadSep hd A,
            pcLtPStar := fun r hr => (A.family r hr).1.2,
            orientation := arcMaps_orientation hd A,
            noFlatTie := arcMaps_noFlatTie hd A,
            brokenSide := arcMaps_brokenSide hd A }, A.mem, ?_⟩
  exact A.notExc r₀ A.mem

end UpperTailOptimizers
