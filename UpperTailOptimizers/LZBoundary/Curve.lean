import UpperTailOptimizers.LZBoundary.Existence

/-!
# The global Lubetzky–Zhao boundary curve

`LZBoundary/Existence.lean` produces, around every non-exceptional `r₀ ∈ (0,1)`, *a* Lubetzky–Zhao boundary arc
`M : LZBoundaryArc d` carrying a boundary curve `M.pc` and a second-contact map `M.sm`.  This
file removes the arc from the picture, which is what Section 3 of `paper/paper.tex`
(Theorem 3.1 and the discussion after it) actually asserts:

* `LZBoundaryArc.pc_unique` / `LZBoundaryArc.sm_unique` — any two arcs agree on the overlap of
  their domains, so there is only **one** boundary curve and one second-contact map.
* `pcGlobal` — a choice-free `sInf` definition of that curve, valid on *all* of `(0,1)`,
  and `pcGlobal_eq_pc`, the bridge saying every arc's `pc` is its restriction.
* `pcGlobal_rStar : pcGlobal d r_* = p_*` and `smGlobal_rStar : smGlobal d r_* = r_*` — the
  **continuous extension across the exceptional density** `r_*`, together with
  `continuousAt_pcGlobal_rStar`, `analyticAt_pcGlobal`, `continuousOn_pcGlobal` and their
  second-contact counterparts `continuousAt_smGlobal_rStar`, `analyticAt_smGlobal`,
  `continuousOn_smGlobal`.
* `lz_boundary_M2_global` — with that extension, condition (M2) holds at *every* `r ∈ (0,1)`:
  a supporting line of `φ_{p,d}` touches at `x = r^d` iff `p ≥ pcGlobal d r`.

The mathematical input that makes the exceptional point work is
`convexOn_phi_of_pStar_le` (`lem:convexity-defect`(e), proved in `LZBoundary/PhiDeriv.lean`): above the
threshold `p_*` the Lubetzky–Zhao graph `φ_{p,d}` is convex on all of `[0,1]`, so *every*
interior abscissa carries a supporting line; and `no_supporting_rStar`: below `p_*` the
exceptional abscissa `r_*^d` lies strictly inside the detached component of the convex
minorant, so no supporting line touches there.
-/

namespace UpperTailOptimizers

open Set Filter Topology

/-! ### Uniqueness of the boundary data -/

/-- The supporting line of (M3) of Theorem 3.1, transported to the `x`-coordinate: at `r ∈ U` the boundary
parameter `pc r` admits a supporting line of `φ_{pc r,d}` at `x = r^d`.  This is the shape
consumed by `brokenSide`, `orientation` and the `lubetzkyZhao` axiom. -/
theorem LZBoundaryArc.supporting_x {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U) :
    ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1,
      Jp (M.pc r) r + a * (x - r ^ d) ≤ phi (M.pc r) d x := by
  have hd0 : (d:ℕ) ≠ 0 := by omega
  refine ⟨slope d M.pc r, fun x hx => ?_⟩
  have hu0 : (0:ℝ) ≤ Real.rpow x (1/(d:ℝ)) := Real.rpow_nonneg hx.1 _
  have hu1 : Real.rpow x (1/(d:ℝ)) ≤ 1 := Real.rpow_le_one hx.1 hx.2 (by positivity)
  have hud : (Real.rpow x (1/(d:ℝ))) ^ d = x := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hx.1 hd0
  have h := M.supporting r hr (Real.rpow x (1/(d:ℝ))) ⟨hu0, hu1⟩
  rw [hud] at h
  exact h

/-- **Uniqueness of the Lubetzky–Zhao boundary curve.**  Any two Lubetzky–Zhao boundary arcs agree on the
overlap of their domains: if `M.pc r < M'.pc r` then `M`'s supporting line at `M.pc r`
contradicts `M'`'s `brokenSide`, and symmetrically. -/
theorem LZBoundaryArc.pc_unique {d : ℕ} (hd : 2 ≤ d) (M M' : LZBoundaryArc d) {r : ℝ}
    (hr : r ∈ M.U) (hr' : r ∈ M'.U) : M.pc r = M'.pc r := by
  rcases lt_trichotomy (M.pc r) (M'.pc r) with h | h | h
  · exact absurd (M.supporting_x hd hr) (M'.brokenSide r hr' (M.pc r) (M.ordering r hr).1 h)
  · exact h
  · exact absurd (M'.supporting_x hd hr') (M.brokenSide r hr (M'.pc r) (M'.ordering r hr').1 h)

/-- **Uniqueness of the second-contact map.**  Once `pc_unique` makes the two supporting
lines identical, `M`'s `quadSep` field ((M5) of Theorem 3.1) evaluated at `M'.sm r` — where
`M'`'s `secondContact` field makes the gap vanish — forces `M'.sm r ∈ {r, M.sm r}`, and `M'.sm r ≠ r`. -/
theorem LZBoundaryArc.sm_unique {d : ℕ} (hd : 2 ≤ d) (M M' : LZBoundaryArc d) {r : ℝ}
    (hr : r ∈ M.U) (hr' : r ∈ M'.U) : M.sm r = M'.sm r := by
  have hpc : M.pc r = M'.pc r := LZBoundaryArc.pc_unique hd M M' hr hr'
  have hslope : slope d M.pc r = slope d M'.pc r := by simp only [slope, hpc]
  obtain ⟨hpc0, hpcr, _hr1, _hsmne, hsm0, _hsm1⟩ := M.ordering r hr
  obtain ⟨_, _, _, hsmne', hsm0', hsm1'⟩ := M'.ordering r hr'
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  obtain ⟨γ, hγ0, hquad⟩ := M.quadSep {r} (by simpa using hr) isCompact_singleton
  -- the gap vanishes at `M'.sm r`
  have hgap : Jp (M.pc r) (M'.sm r)
      - (Jp (M.pc r) r + slope d M.pc r * ((M'.sm r) ^ d - r ^ d)) = 0 := by
    rw [hpc, hslope]; linarith [M'.secondContact r hr']
  have hkey := hquad r rfl (M'.sm r) ⟨hsm0'.le, hsm1'.le⟩
  rw [hgap] at hkey
  -- so the min of the two distances is zero
  obtain ⟨A, hA⟩ : ∃ x : ℝ, x = |(M'.sm r) ^ d - r ^ d| := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x : ℝ, x = |(M'.sm r) ^ d - (M.sm r) ^ d| := ⟨_, rfl⟩
  rw [← hA, ← hB] at hkey
  have hm0 : 0 ≤ min A B := le_min (hA ▸ abs_nonneg _) (hB ▸ abs_nonneg _)
  have hsq : (min A B) ^ 2 = 0 := le_antisymm (by nlinarith [hkey, hγ0]) (sq_nonneg _)
  have hmin : min A B = 0 := by rwa [sq_eq_zero_iff] at hsq
  -- the first distance is nonzero
  have hne1 : A ≠ 0 := by
    rw [hA, abs_ne_zero, sub_ne_zero]
    intro hcon
    exact hsmne' ((pow_left_inj₀ hsm0'.le hr0.le (by omega)).mp hcon)
  have h2 : B = 0 := by
    rcases min_cases A B with ⟨he, _⟩ | ⟨he, _⟩
    · exact absurd (he ▸ hmin) hne1
    · rw [← he]; exact hmin
  rw [hB, abs_eq_zero, sub_eq_zero] at h2
  exact ((pow_left_inj₀ hsm0'.le hsm0.le (by omega)).mp h2).symm

/-! ### Supporting lines above and below the threshold -/

/-- Above the threshold every interior abscissa `r^d` carries a supporting line. -/
theorem supporting_of_pStar_le {d : ℕ} (hd : 2 ≤ d) {p r : ℝ} (hps : pStar d ≤ p) (hp1 : p < 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x := by
  have hrd : r ^ d ∈ Set.Ioo (0:ℝ) 1 := ⟨pow_pos hr0 d, pow_lt_one₀ hr0.le hr1 (by omega)⟩
  obtain ⟨m, hm⟩ := convexOn_supporting_line (convexOn_phi_of_pStar_le hd hps hp1) hrd
  refine ⟨m, fun x hx => ?_⟩
  have h := hm x hx
  rw [Jp_eq_phi_pow hd hr0.le]
  linarith [h]

/-- Below the threshold no supporting line touches at the exceptional abscissa `r_*^d`: it
lies strictly inside the detached component of the convex minorant. -/
theorem no_supporting_rStar {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp : p < pStar d) :
    ¬ ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1,
      Jp p (rStar d) + a * (x - (rStar d) ^ d) ≤ phi p d x := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  obtain ⟨xa, xb, -, -, -, -, -, hxaS, hSxb, -, -, -, -, -, -, hLlt⟩ :=
    lz_boundary_contacts hd hp0 hp
  rintro ⟨a, ha⟩
  have hrIoo : (rStar d) ^ d ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨pow_pos hus0 d, pow_lt_one₀ hus0.le hus1 (by omega)⟩
  have hiff := exists_supportingLine_iff_lce_eq (show (0:ℝ) < 1 by norm_num)
    (phi_continuousOn_Icc hd hp0 hp1) hrIoo
  have hsupp : ∃ s : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1,
      phi p d ((rStar d) ^ d) + s * (x - (rStar d) ^ d) ≤ phi p d x :=
    ⟨a, fun x hx => by have h := ha x hx; rwa [Jp_eq_phi_pow hd hus0.le] at h⟩
  have hxb : xa < (rStar d) ^ d ∧ (rStar d) ^ d < xb := ⟨hxaS, hSxb⟩
  linarith [hiff.mp hsupp, hLlt ((rStar d) ^ d) hxb]

/-! ### The global boundary curve -/

/-- **The global Lubetzky–Zhao boundary curve.**  `pcGlobal d r` is the infimum of the set of
background densities `p > 0` at which `(r^d, J_p(r))` still lies on the convex minorant of
`φ_{p,d}` — equivalently, at which a supporting line touches there.  The defining predicate
is verbatim the right-hand side of the `lubetzkyZhao` dichotomy, so the definition is both
choice-free and exactly the paper's description of the boundary. -/
noncomputable def pcGlobal (d : ℕ) (r : ℝ) : ℝ :=
  sInf {p : ℝ | 0 < p ∧ ∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1,
    Jp p r + a * (x - r ^ d) ≤ phi p d x}

/-- Every Lubetzky–Zhao boundary arc's boundary curve is the restriction of `pcGlobal`: membership comes
from the `ordering` and `supporting` fields, the lower bound from `brokenSide`. -/
theorem pcGlobal_eq_pc {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U) :
    pcGlobal d r = M.pc r := by
  refine IsLeast.csInf_eq ⟨⟨(M.ordering r hr).1, M.supporting_x hd hr⟩, ?_⟩
  rintro p ⟨hp0, hsupp⟩
  by_contra hcon
  push Not at hcon
  exact M.brokenSide r hr p hp0 hcon hsupp

/-- **The continuous extension at the exceptional density**: `pc(r_*) = p_*`. -/
theorem pcGlobal_rStar {d : ℕ} (hd : 2 ≤ d) : pcGlobal d (rStar d) = pStar d := by
  refine IsLeast.csInf_eq ⟨⟨pStar_pos hd,
    supporting_of_pStar_le hd le_rfl (pStar_lt_one hd) (rStar_pos hd) (rStar_lt_one hd)⟩, ?_⟩
  rintro p ⟨hp0, hsupp⟩
  by_contra hcon
  push Not at hcon
  exact no_supporting_rStar hd hp0 hcon hsupp

/-- **Condition (M2), globally.**  With the continuous extension `pcGlobal`, the point
`(r^d, J_p(r))` lies on the convex minorant of `φ_{p,d}` if and only if `p ≥ pcGlobal d r`,
for **every** `r ∈ (0,1)` — including the exceptional density, where no Lubetzky–Zhao boundary arc exists.
This is the closing clause of Theorem 3.1 of `paper/paper.tex`. -/
theorem lz_boundary_M2_global {d : ℕ} (hd : 2 ≤ d) {r p : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∃ a : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, Jp p r + a * (x - r ^ d) ≤ phi p d x)
      ↔ pcGlobal d r ≤ p := by
  by_cases hexc : r = rStar d
  · subst hexc
    rw [pcGlobal_rStar hd]
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      exact no_supporting_rStar hd hp0 hcon h
    · intro h
      exact supporting_of_pStar_le hd h hp1 hr0 hr1
  · obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
    rw [pcGlobal_eq_pc hd M hrU]
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      exact M.brokenSide r hrU p hp0 hcon h
    · intro h
      rcases eq_or_lt_of_le h with heq | hlt
      · rw [← heq]; exact M.supporting_x hd hrU
      · by_cases hps : p < pStar d
        · exact M.orientation r hrU p hlt hps
        · exact supporting_of_pStar_le hd (not_lt.mp hps) hp1 hr0 hr1

/-! ### The global second-contact map -/

/-- The contact set of the supporting line at `r^d` for the background density `p`: the set
of `s ∈ [0,1]` at which the graph of `J_p` meets that line.  The slope expression is
definitionally `slope d (fun _ => p) r`. -/
def contactSet (d : ℕ) (p r : ℝ) : Set ℝ :=
  {s | s ∈ Set.Icc (0:ℝ) 1 ∧
    Jp p s = Jp p r + (Jp' p r / ((d:ℝ) * r ^ (d - 1))) * (s ^ d - r ^ d)}

/-- **The contact set on an arc is the two-point set `{r, s(r)}`** — condition (M4) of
Theorem 3.1: `⊇` is the `ordering` and `secondContact` fields, `⊆` is the `quadSep`
field (M5). -/
theorem LZBoundaryArc.contactSet_eq {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ}
    (hr : r ∈ M.U) : contactSet d (M.pc r) r = {r, M.sm r} := by
  obtain ⟨hpc0, hpcr, hr1, _hsmne, hsm0, hsm1⟩ := M.ordering r hr
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  have hsl : Jp' (M.pc r) r / ((d:ℝ) * r ^ (d - 1)) = slope d M.pc r := rfl
  obtain ⟨γ, hγ0, hquad⟩ := M.quadSep {r} (by simpa using hr) isCompact_singleton
  ext s
  simp only [contactSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hsl]
  constructor
  · rintro ⟨hs01, hs⟩
    have hkey := hquad r rfl s hs01
    rw [hs] at hkey
    simp only [sub_self] at hkey
    obtain ⟨A, hA⟩ : ∃ x : ℝ, x = |s ^ d - r ^ d| := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ x : ℝ, x = |s ^ d - (M.sm r) ^ d| := ⟨_, rfl⟩
    rw [← hA, ← hB] at hkey
    have hm0 : 0 ≤ min A B := le_min (hA ▸ abs_nonneg _) (hB ▸ abs_nonneg _)
    have hsq : (min A B) ^ 2 = 0 := le_antisymm (by nlinarith [hkey, hγ0]) (sq_nonneg _)
    have hmin : min A B = 0 := by rwa [sq_eq_zero_iff] at hsq
    rcases min_cases A B with ⟨he, -⟩ | ⟨he, -⟩
    · left
      have hpw : s ^ d = r ^ d := by
        have h := he ▸ hmin; rw [hA, abs_eq_zero, sub_eq_zero] at h; exact h
      exact (pow_left_inj₀ hs01.1 hr0.le (by omega)).mp hpw
    · right
      have hpw : s ^ d = (M.sm r) ^ d := by
        have h := he ▸ hmin; rw [hB, abs_eq_zero, sub_eq_zero] at h; exact h
      exact (pow_left_inj₀ hs01.1 hsm0.le (by omega)).mp hpw
  · rintro (rfl | rfl)
    · exact ⟨⟨hr0.le, hr1.le⟩, by ring⟩
    · exact ⟨⟨hsm0.le, hsm1.le⟩, M.secondContact r hr⟩

/-- **The global second-contact map.**  The contact set is the two-point set `{r, s(r)}`,
degenerating to the singleton `{r_*}` at the exceptional density; `min C + max C - r` picks
out the *other* element, and returns `r` itself when the two contacts merge.  (The prettier
`sSup (C \ {r})` would be wrong at `r_*`, where that set is empty and the supremum is `0`.) -/
noncomputable def smGlobal (d : ℕ) (r : ℝ) : ℝ :=
  sInf (contactSet d (pcGlobal d r) r) + sSup (contactSet d (pcGlobal d r) r) - r

/-- Every arc's second-contact map is the restriction of `smGlobal`. -/
theorem smGlobal_eq_sm {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U) :
    smGlobal d r = M.sm r := by
  rw [smGlobal, pcGlobal_eq_pc hd M hr, M.contactSet_eq hd hr, csInf_pair, csSup_pair]
  show min r (M.sm r) + max r (M.sm r) - r = M.sm r
  linarith [min_add_max r (M.sm r)]

/-- At the threshold the two contacts merge: the contact set is the singleton `{r_*}`.
Strict convexity of `φ_{p_*,d}` on each side of `r_*^d` keeps the tangent there strictly
below the graph elsewhere. -/
theorem contactSet_pStar_rStar {d : ℕ} (hd : 2 ≤ d) :
    contactSet d (pStar d) (rStar d) = {rStar d} := by
  have hp0 := pStar_pos hd
  have hp1 := pStar_lt_one hd
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  have hd0 : d ≠ 0 := by omega
  obtain ⟨c, hc⟩ : ∃ x : ℝ, x = (rStar d) ^ d := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ pow_pos hus0 d
  have hc1 : c < 1 := hc ▸ pow_lt_one₀ hus0.le hus1 hd0
  have hstar0 : hpd (pStar d) d (rStar d) = 0 := (hpd_rStar_eq_zero_iff hd hp0 hp1).mpr rfl
  -- `φ'' > 0` strictly on each side of `c`
  have hleft : ∀ x ∈ Set.Ioo (0:ℝ) c, 0 < phi'' (pStar d) d x := by
    intro x hx
    have hu0 : 0 < Real.rpow x (1/(d:ℝ)) := Real.rpow_pos_of_pos hx.1 _
    have hulow : Real.rpow x (1/(d:ℝ)) < rStar d := by
      have h : x ^ (1/(d:ℝ)) < ((rStar d) ^ d) ^ (1/(d:ℝ)) :=
        Real.rpow_lt_rpow hx.1.le (hc ▸ hx.2) (show (0:ℝ) < 1/(d:ℝ) by
          have := dpos hd; positivity)
      have he : ((rStar d) ^ d : ℝ) ^ (1/(d:ℝ)) = rStar d := by
        rw [one_div]; exact Real.pow_rpow_inv_natCast hus0.le hd0
      rw [he] at h; exact h
    rw [phi''_pos_iff hd hx.1, ← hstar0]
    exact hpd_strictAntiOn_Ioc hd hp0 hp1 ⟨hu0, hulow.le⟩ ⟨hus0, le_rfl⟩ hulow
  have hright : ∀ x ∈ Set.Ioo c 1, 0 < phi'' (pStar d) d x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hc0 hx.1
    have hu1 : Real.rpow x (1/(d:ℝ)) < 1 := by
      have h : Real.rpow x (1/(d:ℝ)) < Real.rpow 1 (1/(d:ℝ)) :=
        Real.rpow_lt_rpow hx0.le hx.2 (by have := dpos hd; positivity)
      simpa using h
    have huhigh : rStar d < Real.rpow x (1/(d:ℝ)) := by
      have h : ((rStar d) ^ d) ^ (1/(d:ℝ)) < x ^ (1/(d:ℝ)) :=
        Real.rpow_lt_rpow (hc ▸ hc0.le) (hc ▸ hx.1) (show (0:ℝ) < 1/(d:ℝ) by
          have := dpos hd; positivity)
      have he : ((rStar d) ^ d : ℝ) ^ (1/(d:ℝ)) = rStar d := by
        rw [one_div]; exact Real.pow_rpow_inv_natCast hus0.le hd0
      rw [he] at h; exact h
    rw [phi''_pos_iff hd hx0, ← hstar0]
    exact hpd_strictMonoOn_Ico hd hp0 hp1 ⟨le_rfl, hus1⟩ ⟨huhigh.le, hu1⟩ huhigh
  have hderiv : HasDerivAt (phi (pStar d) d) (deriv (phi (pStar d) d) c) c := by
    have h := hasDerivAt_phi hd hp0 hp1 hc0 hc1; rw [h.deriv]; exact h
  have hsL := strictConvexOn_phi_left hd hp0 hp1 hc0 hc1 hleft
  have hsR := strictConvexOn_phi_right hd hp0 hp1 hc0 hc1 hright
  ext s
  simp only [contactSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hs01, hs⟩
    by_contra hne
    have hsd : s ^ d ≠ c := by
      rw [hc]; intro hcon; exact hne ((pow_left_inj₀ hs01.1 hus0.le hd0).mp hcon)
    have hsl : Jp' (pStar d) (rStar d) / ((d:ℝ) * (rStar d) ^ (d - 1))
        = deriv (phi (pStar d) d) c := by
      rw [hc]; exact slope_eq_deriv_phi (pc := fun _ => pStar d) hd hp0 hp1 hus0 hus1
    rw [hsl, Jp_eq_phi_pow hd hs01.1, Jp_eq_phi_pow hd hus0.le, ← hc] at hs
    have hsdIcc : s ^ d ∈ Set.Icc (0:ℝ) 1 :=
      ⟨pow_nonneg hs01.1 d, pow_le_one₀ hs01.1 hs01.2⟩
    rcases lt_trichotomy (s ^ d) c with h | h | h
    · exact absurd hs (ne_of_gt (strictConvexOn_tangent_lt hsL ⟨hc0.le, le_rfl⟩ hderiv
        (s ^ d) ⟨hsdIcc.1, h.le⟩ hsd))
    · exact hsd h
    · exact absurd hs (ne_of_gt (strictConvexOn_tangent_lt hsR ⟨le_rfl, hc1.le⟩ hderiv
        (s ^ d) ⟨h.le, hsdIcc.2⟩ hsd))
  · rintro rfl
    exact ⟨⟨hus0.le, hus1.le⟩, by ring⟩

/-- **The continuous extension at the exceptional density**: `s(r_*) = r_*`. -/
theorem smGlobal_rStar {d : ℕ} (hd : 2 ≤ d) : smGlobal d (rStar d) = rStar d := by
  rw [smGlobal, pcGlobal_rStar hd, contactSet_pStar_rStar hd, csInf_singleton, csSup_singleton]
  ring

/-! ### Continuity and analyticity of the extended boundary curve -/

/-- `0 < pcGlobal d r ≤ p_*` on `(0,1)`. -/
theorem pcGlobal_pos_le {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < pcGlobal d r ∧ pcGlobal d r ≤ pStar d := by
  by_cases hexc : r = rStar d
  · subst hexc; rw [pcGlobal_rStar hd]; exact ⟨pStar_pos hd, le_rfl⟩
  · obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
    rw [pcGlobal_eq_pc hd M hrU]
    exact ⟨(M.ordering r hrU).1, (M.pcLtPStar r hrU).le⟩

/-- Off the exceptional density the boundary curve stays *strictly* below the threshold. -/
theorem pcGlobal_lt_pStar {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hexc : r ≠ rStar d) : pcGlobal d r < pStar d := by
  obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
  rw [pcGlobal_eq_pc hd M hrU]
  exact M.pcLtPStar r hrU

/-- Below the threshold no supporting line touches strictly between the two Lubetzky–Zhao contacts
of the parameter `c`; the preimage of the detached interval under `r ↦ r^d` is therefore an
**open neighbourhood of `r_*` on which `pcGlobal > c`**.  This is the soft ingredient of
continuity at the exceptional density (it needs no inversion of the contact maps). -/
theorem lt_pcGlobal_of_between {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 < c) (hc : c < pStar d) :
    ∃ V : Set ℝ, IsOpen V ∧ rStar d ∈ V ∧ ∀ r ∈ V, 0 < r → r < 1 → c < pcGlobal d r := by
  have hc1 : c < 1 := lt_trans hc (pStar_lt_one hd)
  obtain ⟨xa, xb, -, -, -, -, -, hxaS, hSxb, -, -, -, -, -, -, hLlt⟩ :=
    lz_boundary_contacts hd hc0 hc
  refine ⟨(fun r : ℝ => r ^ d) ⁻¹' (Set.Ioo xa xb),
    (isOpen_Ioo.preimage (by fun_prop)), ⟨hxaS, hSxb⟩, ?_⟩
  intro r hrV hr0 hr1
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := (lz_boundary_M2_global hd hr0 hr1 hc0 hc1).mpr hcon
  have hrIoo : r ^ d ∈ Set.Ioo (0:ℝ) 1 := ⟨pow_pos hr0 d, pow_lt_one₀ hr0.le hr1 (by omega)⟩
  have hiff := exists_supportingLine_iff_lce_eq (show (0:ℝ) < 1 by norm_num)
    (phi_continuousOn_Icc hd hc0 hc1) hrIoo
  have hsupp' : ∃ s : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1,
      phi c d (r ^ d) + s * (x - r ^ d) ≤ phi c d x :=
    ⟨a, fun x hx => by have h := ha x hx; rwa [Jp_eq_phi_pow hd hr0.le] at h⟩
  linarith [hiff.mp hsupp', hLlt (r ^ d) hrV]

/-- **The boundary curve is continuous at the exceptional density**, with value `p_*`. -/
theorem continuousAt_pcGlobal_rStar {d : ℕ} (hd : 2 ≤ d) :
    ContinuousAt (pcGlobal d) (rStar d) := by
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  rw [ContinuousAt, pcGlobal_rStar hd, tendsto_order]
  constructor
  · intro c hc
    by_cases hc0 : 0 < c
    · obtain ⟨V, hVopen, hVmem, hV⟩ := lt_pcGlobal_of_between hd hc0 hc
      filter_upwards [hVopen.mem_nhds hVmem,
        isOpen_Ioo.mem_nhds (show rStar d ∈ Set.Ioo (0:ℝ) 1 from ⟨hus0, hus1⟩)] with r hrV hr
      exact hV r hrV hr.1 hr.2
    · filter_upwards [isOpen_Ioo.mem_nhds (show rStar d ∈ Set.Ioo (0:ℝ) 1 from ⟨hus0, hus1⟩)]
        with r hr
      exact lt_of_le_of_lt (not_lt.mp hc0) (pcGlobal_pos_le hd hr.1 hr.2).1
  · intro c hc
    filter_upwards [isOpen_Ioo.mem_nhds (show rStar d ∈ Set.Ioo (0:ℝ) 1 from ⟨hus0, hus1⟩)]
      with r hr
    exact lt_of_le_of_lt (pcGlobal_pos_le hd hr.1 hr.2).2 hc

/-- `pcGlobal` is analytic off the exceptional density. -/
theorem analyticAt_pcGlobal {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hexc : r ≠ rStar d) : AnalyticAt ℝ (pcGlobal d) r := by
  obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
  refine (M.analytic_pc r hrU).congr ?_
  filter_upwards [M.isOpen_U.mem_nhds hrU] with s hs
  exact (pcGlobal_eq_pc hd M hs).symm

/-- **The boundary curve is continuous on all of `(0,1)`.** -/
theorem continuousOn_pcGlobal {d : ℕ} (hd : 2 ≤ d) :
    ContinuousOn (pcGlobal d) (Set.Ioo 0 1) := by
  intro r hr
  by_cases hexc : r = rStar d
  · subst hexc; exact (continuousAt_pcGlobal_rStar hd).continuousWithinAt
  · exact (analyticAt_pcGlobal hd hr.1 hr.2 hexc).continuousAt.continuousWithinAt

/-! ### Continuity of the second-contact map at the exceptional density

The remaining clause of Theorem 3.1's continuous-extension statement.  The mathematical
content is that off the exceptional density the pair `{r^d, s(r)^d}` is *exactly* the
Lubetzky–Zhao contact pair `{u_a(pc r)^d, u_b(pc r)^d}` (`contact_mem_lz_boundary`); the contacts are
then squeezed towards `r_*^d` by any two flanking abscissae whose own boundary values are
already below `pc(r)`, which `continuousAt_pcGlobal_rStar` makes available. -/

/-- An affine function that is nonnegative at the two endpoints of a segment is nonnegative
on the segment. -/
private theorem affine_nonneg_between {α β x1 x2 t : ℝ} (h1 : 0 ≤ α * x1 + β)
    (h2 : 0 ≤ α * x2 + β) (ht1 : x1 ≤ t) (ht2 : t ≤ x2) : 0 ≤ α * t + β := by
  by_cases hα : 0 ≤ α
  · nlinarith [h1, ht1]
  · push Not at hα
    nlinarith [h2, ht2]

/-- **A supporting line with two contacts is the Lubetzky–Zhao supporting line.**  For `0 < p < p_*`, if an
affine minorant of `φ_{p,d}` on `[0,1]` touches the graph at two distinct interior points
`x1 ≠ x2`, then `x2` is one of the two Lubetzky–Zhao contacts `x_a = u_a(p)^d`, `x_b = u_b(p)^d`.

Proof: neither contact lies in the detached component `(x_a,x_b)` (there `lce < φ`), and
`φ_{p,d}` is strictly convex on `[0,x_a]` and on `[x_b,1]`, so the two contacts cannot lie
on the same convex piece.  Hence `x_a` and `x_b` lie between them, and the affine difference
of the two minorants — nonnegative at `x1, x2` and nonpositive at `x_a, x_b` — vanishes
identically.  The two lines coincide, and `gap_pos_abstract` pins `x2` to a contact. -/
theorem contact_mem_lz_boundary {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {p : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) {x1 x2 m : ℝ}
    (hx1 : x1 ∈ Set.Ioo (0:ℝ) 1) (hx2 : x2 ∈ Set.Ioo (0:ℝ) 1) (hne : x1 ≠ x2)
    (hmin : ∀ t ∈ Set.Icc (0:ℝ) 1, phi p d x1 + m * (t - x1) ≤ phi p d t)
    (htouch : phi p d x1 + m * (x2 - x1) = phi p d x2) :
    x2 = (G.ua p) ^ d ∨ x2 = (G.ub p) ^ d := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  obtain ⟨hxa0, hxa_xb, hxb1, hHxa, hHxb, hchord, hsupp, hconvL, hconvR, hlce, -, -⟩ :=
    contact_bundle hd G hp0 hp
  obtain ⟨xa, hxadef⟩ : ∃ x : ℝ, x = (G.ua p) ^ d := ⟨_, rfl⟩
  obtain ⟨xb, hxbdef⟩ : ∃ x : ℝ, x = (G.ub p) ^ d := ⟨_, rfl⟩
  simp only [← hxadef, ← hxbdef] at hxa0 hxa_xb hxb1 hHxa hHxb hchord hsupp hconvL hconvR hlce
  obtain ⟨mm, hmmdef⟩ : ∃ x : ℝ, x = deriv (phi p d) xa := ⟨_, rfl⟩
  simp only [← hmmdef] at hHxa hHxb hchord hsupp
  have hxa1 : xa < 1 := lt_trans hxa_xb hxb1
  have hxb0 : (0:ℝ) < xb := lt_trans hxa0 hxa_xb
  have hx1Icc : x1 ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hx1
  have hx2Icc : x2 ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hx2
  have hxaIcc : xa ∈ Set.Icc (0:ℝ) 1 := ⟨hxa0.le, hxa1.le⟩
  have hxbIcc : xb ∈ Set.Icc (0:ℝ) 1 := ⟨hxb0.le, hxb1.le⟩
  have hcont := phi_continuousOn_Icc hd hp0 hp1
  -- the same affine line is a supporting line at `x2`
  have hmin2 : ∀ t ∈ Set.Icc (0:ℝ) 1, phi p d x2 + m * (t - x2) ≤ phi p d t := by
    intro t ht; have h := hmin t ht; linarith [htouch]
  -- neither contact lies strictly between the Lubetzky–Zhao contacts
  have hout : ∀ y : ℝ, y ∈ Set.Ioo (0:ℝ) 1 →
      (∀ t ∈ Set.Icc (0:ℝ) 1, phi p d y + m * (t - y) ≤ phi p d t) → y ≤ xa ∨ xb ≤ y := by
    intro y hy hminy
    by_contra hcon
    push Not at hcon
    have heq := (exists_supportingLine_iff_lce_eq (show (0:ℝ) < 1 by norm_num) hcont hy).mp
      ⟨m, hminy⟩
    linarith [hlce y ⟨hcon.1, hcon.2⟩, heq]
  have h1out := hout x1 hx1 hmin
  have h2out := hout x2 hx2 hmin2
  -- the slope of the minorant is the derivative at `x1`
  have hderiv1 : HasDerivAt (phi p d) m x1 := by
    have hH : HasDerivAt (phi p d) (deriv (phi p d) x1) x1 := by
      have h := hasDerivAt_phi hd hp0 hp1 hx1.1 hx1.2; rw [h.deriv]; exact h
    have hmt : ∀ t ∈ Set.Icc (0:ℝ) 1, m * t + (phi p d x1 - m * x1) ≤ phi p d t := by
      intro t ht; have h := hmin t ht; linarith
    have hm := tangent_of_affineMinorant hmt hx1 (by ring) hH
    rwa [hm] at hH
  -- `α t + β` is the difference of the two affine minorants
  obtain ⟨α, hα⟩ : ∃ x : ℝ, x = m - mm := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ x : ℝ, x = (phi p d x1 - m * x1) - (phi p d xa - mm * xa) := ⟨_, rfl⟩
  have gx1 : 0 ≤ α * x1 + β := by
    have h := hsupp x1 hx1Icc; rw [hα, hβ]; nlinarith [h]
  have gx2 : 0 ≤ α * x2 + β := by
    have h := hsupp x2 hx2Icc; rw [hα, hβ]; nlinarith [h, htouch]
  have gxa : α * xa + β ≤ 0 := by
    have h := hmin xa hxaIcc; rw [hα, hβ]; nlinarith [h]
  have gxb : α * xb + β ≤ 0 := by
    have h := hmin xb hxbIcc; rw [hα, hβ]; nlinarith [h, hchord]
  rcases h1out with h1 | h1
  · rcases h2out with h2 | h2
    · -- both contacts on the left convex piece: impossible
      exfalso
      have hsconv : StrictConvexOn ℝ (Set.Icc 0 xa) (phi p d) :=
        strictConvexOn_phi_left hd hp0 hp1 hxa0 hxa1 hconvL
      have h := strictConvexOn_tangent_lt hsconv ⟨hx1.1.le, h1⟩ hderiv1 x2 ⟨hx2.1.le, h2⟩
        (Ne.symm hne)
      linarith [htouch, h]
    · -- `xa` and `xb` lie between `x1` and `x2`: the two minorants coincide
      have hxaz : α * xa + β = 0 :=
        le_antisymm gxa (affine_nonneg_between gx1 gx2 h1 (le_trans hxa_xb.le h2))
      have hxbz : α * xb + β = 0 :=
        le_antisymm gxb (affine_nonneg_between gx1 gx2 (le_trans h1 hxa_xb.le) h2)
      have hα0 : α = 0 := by
        have hz : α * (xa - xb) = 0 := by linarith
        rcases mul_eq_zero.mp hz with h | h
        · exact h
        · exact absurd (by linarith : xa = xb) (ne_of_lt hxa_xb)
      have hβ0 : β = 0 := by rw [hα0] at hxaz; linarith
      by_contra hcon
      push Not at hcon
      have hgap := gap_pos_abstract hd hp0 hp1 hxa0 hxa_xb hxb1 hHxa hHxb hchord hsupp
        hconvL hconvR hlce hx2Icc.1 hx2Icc.2 (by rw [hxadef]; exact hcon.1)
        (by rw [hxbdef]; exact hcon.2)
      have hz : α * x2 + β = 0 := by rw [hα0, hβ0]; ring
      rw [hα, hβ] at hz
      nlinarith [hgap, htouch, hz]
  · rcases h2out with h2 | h2
    · -- `xa` and `xb` lie between `x2` and `x1`: the two minorants coincide
      have hxaz : α * xa + β = 0 :=
        le_antisymm gxa (affine_nonneg_between gx2 gx1 h2 (le_trans hxa_xb.le h1))
      have hxbz : α * xb + β = 0 :=
        le_antisymm gxb (affine_nonneg_between gx2 gx1 (le_trans h2 hxa_xb.le) h1)
      have hα0 : α = 0 := by
        have hz : α * (xa - xb) = 0 := by linarith
        rcases mul_eq_zero.mp hz with h | h
        · exact h
        · exact absurd (by linarith : xa = xb) (ne_of_lt hxa_xb)
      have hβ0 : β = 0 := by rw [hα0] at hxaz; linarith
      by_contra hcon
      push Not at hcon
      have hgap := gap_pos_abstract hd hp0 hp1 hxa0 hxa_xb hxb1 hHxa hHxb hchord hsupp
        hconvL hconvR hlce hx2Icc.1 hx2Icc.2 (by rw [hxadef]; exact hcon.1)
        (by rw [hxbdef]; exact hcon.2)
      have hz : α * x2 + β = 0 := by rw [hα0, hβ0]; ring
      rw [hα, hβ] at hz
      nlinarith [hgap, htouch, hz]
    · -- both contacts on the right convex piece: impossible
      exfalso
      have hsconv : StrictConvexOn ℝ (Set.Icc xb 1) (phi p d) :=
        strictConvexOn_phi_right hd hp0 hp1 hxb0 hxb1 hconvR
      have h := strictConvexOn_tangent_lt hsconv ⟨h1, hx1.2.le⟩ hderiv1 x2 ⟨h2, hx2.2.le⟩
        (Ne.symm hne)
      linarith [htouch, h]

/-- The supporting line at `r^d` and its second contact, in the `x`-coordinate. -/
theorem LZBoundaryArc.contact_data {d : ℕ} (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ}
    (hr : r ∈ M.U) :
    (∀ x ∈ Set.Icc (0:ℝ) 1,
      phi (M.pc r) d (r ^ d) + slope d M.pc r * (x - r ^ d) ≤ phi (M.pc r) d x) ∧
    phi (M.pc r) d (r ^ d) + slope d M.pc r * ((M.sm r) ^ d - r ^ d)
      = phi (M.pc r) d ((M.sm r) ^ d) := by
  obtain ⟨hpc0, hpcr, -, -, hsm0, -⟩ := M.ordering r hr
  have hr0 : 0 < r := lt_trans hpc0 hpcr
  have hd0 : (d:ℕ) ≠ 0 := by omega
  constructor
  · intro x hx
    have hu0 : (0:ℝ) ≤ Real.rpow x (1/(d:ℝ)) := Real.rpow_nonneg hx.1 _
    have hu1 : Real.rpow x (1/(d:ℝ)) ≤ 1 := Real.rpow_le_one hx.1 hx.2 (by positivity)
    have hud : (Real.rpow x (1/(d:ℝ))) ^ d = x := by
      rw [one_div]; exact Real.rpow_inv_natCast_pow hx.1 hd0
    have h := M.supporting r hr (Real.rpow x (1/(d:ℝ))) ⟨hu0, hu1⟩
    rw [hud, Jp_eq_phi_pow hd hu0, hud, Jp_eq_phi_pow hd hr0.le] at h
    exact h
  · have h := M.secondContact r hr
    rw [Jp_eq_phi_pow hd hsm0.le, Jp_eq_phi_pow hd hr0.le] at h
    linarith [h]

/-- **The second contact is a Lubetzky–Zhao contact.**  Off the exceptional density, `s(r)^d` is
one of the two Lubetzky–Zhao contacts of the parameter `pc(r)`. -/
theorem smGlobal_pow_mem {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hexc : r ≠ rStar d) :
    (smGlobal d r) ^ d = (G.ua (pcGlobal d r)) ^ d ∨
      (smGlobal d r) ^ d = (G.ub (pcGlobal d r)) ^ d := by
  obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
  obtain ⟨hpc0, -, -, hsmne, hsm0, hsm1⟩ := M.ordering r hrU
  obtain ⟨hmin, htouch⟩ := M.contact_data hd hrU
  rw [pcGlobal_eq_pc hd M hrU, smGlobal_eq_sm hd M hrU]
  refine contact_mem_lz_boundary hd G hpc0 (M.pcLtPStar r hrU)
    ⟨pow_pos hr0 d, pow_lt_one₀ hr0.le hr1 (by omega)⟩
    ⟨pow_pos hsm0 d, pow_lt_one₀ hsm0.le hsm1 (by omega)⟩ ?_ hmin htouch
  intro hcon
  exact hsmne ((pow_left_inj₀ hsm0.le hr0.le (by omega)).mp hcon.symm)

/-- An abscissa `y < r_*` that already admits a supporting line at parameter `p` bounds the
left Lubetzky–Zhao contact from below. -/
theorem pow_le_ua_pow {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {p y : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) (hy0 : 0 < y) (hy : y < rStar d)
    (hyp : pcGlobal d y ≤ p) : y ^ d ≤ (G.ua p) ^ d := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hy1 : y < 1 := lt_trans hy (rStar_lt_one hd)
  obtain ⟨-, -, hubs, -, -, -, -⟩ := G.contact p hp0 hp
  obtain ⟨-, -, -, -, -, -, -, -, -, hlce, -, -⟩ := contact_bundle hd G hp0 hp
  obtain ⟨a, ha⟩ := (lz_boundary_M2_global hd hy0 hy1 hp0 hp1).mpr hyp
  have hyIoo : y ^ d ∈ Set.Ioo (0:ℝ) 1 := ⟨pow_pos hy0 d, pow_lt_one₀ hy0.le hy1 (by omega)⟩
  have heq := (exists_supportingLine_iff_lce_eq (show (0:ℝ) < 1 by norm_num)
    (phi_continuousOn_Icc hd hp0 hp1) hyIoo).mp
      ⟨a, fun x hx => by have h := ha x hx; rwa [Jp_eq_phi_pow hd hy0.le] at h⟩
  by_contra hcon
  push Not at hcon
  have h1 : y ^ d < (rStar d) ^ d := pow_lt_pow_left₀ hy hy0.le (by omega)
  have h2 : (rStar d) ^ d < (G.ub p) ^ d :=
    pow_lt_pow_left₀ hubs (rStar_pos hd).le (by omega)
  linarith [hlce (y ^ d) ⟨hcon, lt_trans h1 h2⟩, heq]

/-- An abscissa `y > r_*` that already admits a supporting line at parameter `p` bounds the
right Lubetzky–Zhao contact from above. -/
theorem ub_pow_le_pow {d : ℕ} (hd : 2 ≤ d) (G : GlobalContacts d) {p y : ℝ}
    (hp0 : 0 < p) (hp : p < pStar d) (hy : rStar d < y) (hy1 : y < 1)
    (hyp : pcGlobal d y ≤ p) : (G.ub p) ^ d ≤ y ^ d := by
  have hp1 : p < 1 := lt_trans hp (pStar_lt_one hd)
  have hy0 : 0 < y := lt_trans (rStar_pos hd) hy
  obtain ⟨hua0, huas, -, -, -, -, -⟩ := G.contact p hp0 hp
  obtain ⟨-, -, -, -, -, -, -, -, -, hlce, -, -⟩ := contact_bundle hd G hp0 hp
  obtain ⟨a, ha⟩ := (lz_boundary_M2_global hd hy0 hy1 hp0 hp1).mpr hyp
  have hyIoo : y ^ d ∈ Set.Ioo (0:ℝ) 1 := ⟨pow_pos hy0 d, pow_lt_one₀ hy0.le hy1 (by omega)⟩
  have heq := (exists_supportingLine_iff_lce_eq (show (0:ℝ) < 1 by norm_num)
    (phi_continuousOn_Icc hd hp0 hp1) hyIoo).mp
      ⟨a, fun x hx => by have h := ha x hx; rwa [Jp_eq_phi_pow hd hy0.le] at h⟩
  by_contra hcon
  push Not at hcon
  have h1 : (G.ua p) ^ d < (rStar d) ^ d := pow_lt_pow_left₀ huas hua0.le (by omega)
  have h2 : (rStar d) ^ d < y ^ d := pow_lt_pow_left₀ hy (rStar_pos hd).le (by omega)
  linarith [hlce (y ^ d) ⟨lt_trans h1 h2, hcon⟩, heq]

/-- The global second contact stays in `(0,1)`. -/
theorem smGlobal_mem_Ioo {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < smGlobal d r ∧ smGlobal d r < 1 := by
  by_cases hexc : r = rStar d
  · subst hexc; rw [smGlobal_rStar hd]; exact ⟨rStar_pos hd, rStar_lt_one hd⟩
  · obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
    obtain ⟨-, -, -, -, hsm0, hsm1⟩ := M.ordering r hrU
    rw [smGlobal_eq_sm hd M hrU]
    exact ⟨hsm0, hsm1⟩

/-- **The second-contact map is continuous at the exceptional density**, with value `r_*`.
Given `ε > 0`, pick flanking abscissae `y_1 < r_* < y_2` inside the `ε`-window; their
boundary values are `< p_*`, so `pc(r) > max(pc(y_1), pc(y_2))` for `r` near `r_*` by
`continuousAt_pcGlobal_rStar`.  Then `y_1^d ≤ u_a(pc r)^d` and `u_b(pc r)^d ≤ y_2^d`, and
`s(r)^d` is one of those two contacts. -/
theorem continuousAt_smGlobal_rStar {d : ℕ} (hd : 2 ≤ d) :
    ContinuousAt (smGlobal d) (rStar d) := by
  obtain ⟨G⟩ := exists_globalContacts hd
  have hus0 := rStar_pos hd
  have hus1 := rStar_lt_one hd
  rw [ContinuousAt, smGlobal_rStar hd, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y1, hy1def⟩ : ∃ x : ℝ, x = rStar d - min (rStar d / 2) (ε / 2) := ⟨_, rfl⟩
  obtain ⟨y2, hy2def⟩ : ∃ x : ℝ, x = rStar d + min ((1 - rStar d) / 2) (ε / 2) := ⟨_, rfl⟩
  have hm1 : 0 < min (rStar d / 2) (ε / 2) := lt_min (by linarith) (by linarith)
  have hm2 : 0 < min ((1 - rStar d) / 2) (ε / 2) := lt_min (by linarith) (by linarith)
  have hy10 : 0 < y1 := by
    rw [hy1def]; have := min_le_left (rStar d / 2) (ε / 2); linarith
  have hy1s : y1 < rStar d := by rw [hy1def]; linarith
  have hy2s : rStar d < y2 := by rw [hy2def]; linarith
  have hy21 : y2 < 1 := by
    rw [hy2def]; have := min_le_left ((1 - rStar d) / 2) (ε / 2); linarith
  have hy1e : rStar d - y1 < ε := by
    rw [hy1def]; have := min_le_right (rStar d / 2) (ε / 2); linarith
  have hy2e : y2 - rStar d < ε := by
    rw [hy2def]; have := min_le_right ((1 - rStar d) / 2) (ε / 2); linarith
  have hy11 : y1 < 1 := lt_trans hy1s hus1
  have hy20 : 0 < y2 := lt_trans hus0 hy2s
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ, x = max (pcGlobal d y1) (pcGlobal d y2) := ⟨_, rfl⟩
  have hc : c < pStar d := by
    rw [hcdef]
    exact max_lt (pcGlobal_lt_pStar hd hy10 hy11 (ne_of_lt hy1s))
      (pcGlobal_lt_pStar hd hy20 hy21 (ne_of_gt hy2s))
  have hcstar : c < pcGlobal d (rStar d) := by rw [pcGlobal_rStar hd]; exact hc
  have hev := (tendsto_order.mp (continuousAt_pcGlobal_rStar hd)).1 c hcstar
  filter_upwards [hev, isOpen_Ioo.mem_nhds (show rStar d ∈ Set.Ioo (0:ℝ) 1 from ⟨hus0, hus1⟩)]
    with r hcr hr01
  by_cases hexc : r = rStar d
  · subst hexc; rw [smGlobal_rStar hd]; simpa using hε
  · have hp0 : 0 < pcGlobal d r := (pcGlobal_pos_le hd hr01.1 hr01.2).1
    have hp : pcGlobal d r < pStar d := pcGlobal_lt_pStar hd hr01.1 hr01.2 hexc
    have hy1p : pcGlobal d y1 ≤ pcGlobal d r := by
      rw [hcdef] at hcr; exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) hcr)
    have hy2p : pcGlobal d y2 ≤ pcGlobal d r := by
      rw [hcdef] at hcr; exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) hcr)
    have hlow := pow_le_ua_pow hd G hp0 hp hy10 hy1s hy1p
    have hhigh := ub_pow_le_pow hd G hp0 hp hy2s hy21 hy2p
    obtain ⟨hua0, huas, hubs, -, -, -, -⟩ := G.contact _ hp0 hp
    have huab : (G.ua (pcGlobal d r)) ^ d < (G.ub (pcGlobal d r)) ^ d :=
      pow_lt_pow_left₀ (lt_trans huas hubs) hua0.le (by omega)
    obtain ⟨hs0, -⟩ := smGlobal_mem_Ioo hd hr01.1 hr01.2
    have hband : y1 ^ d ≤ (smGlobal d r) ^ d ∧ (smGlobal d r) ^ d ≤ y2 ^ d := by
      rcases smGlobal_pow_mem hd G hr01.1 hr01.2 hexc with h | h
      · exact ⟨by rw [h]; exact hlow, by rw [h]; linarith⟩
      · exact ⟨by rw [h]; linarith, by rw [h]; exact hhigh⟩
    have hle1 : y1 ≤ smGlobal d r :=
      (pow_le_pow_iff_left₀ hy10.le hs0.le (by omega)).mp hband.1
    have hle2 : smGlobal d r ≤ y2 :=
      (pow_le_pow_iff_left₀ hs0.le hy20.le (by omega)).mp hband.2
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩

/-- `smGlobal` is analytic off the exceptional density. -/
theorem analyticAt_smGlobal {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hexc : r ≠ rStar d) : AnalyticAt ℝ (smGlobal d) r := by
  obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
  refine (M.analytic_sm r hrU).congr ?_
  filter_upwards [M.isOpen_U.mem_nhds hrU] with s hs
  exact (smGlobal_eq_sm hd M hs).symm

/-- **The second-contact map is continuous on all of `(0,1)`.** -/
theorem continuousOn_smGlobal {d : ℕ} (hd : 2 ≤ d) :
    ContinuousOn (smGlobal d) (Set.Ioo 0 1) := by
  intro r hr
  by_cases hexc : r = rStar d
  · subst hexc; exact (continuousAt_smGlobal_rStar hd).continuousWithinAt
  · exact (analyticAt_smGlobal hd hr.1 hr.2 hexc).continuousAt.continuousWithinAt

end UpperTailOptimizers
