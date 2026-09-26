import UpperTailOptimizers.LZBoundary.PaperForm

/-!
# The supporting cost gap in the density variable ((M3) of Theorem 3.1)

`sec:lz-boundary` of `paper/paper.tex` measures the failure of the supporting line in the
**density** variable `z` (the coordinate of the Lubetzky–Zhao criterion is `x = z^d`).  For
`r ≠ r_*` it defines the *supporting cost gap* `eq:supporting-cost-gap`

`g_{d,r}(z) = J_{p_c(r)}(z) - ℓ_r(z^d)`,   `ℓ_r(x) = φ_{p_c(r),d}(r^d) + φ_{p_c(r),d}'(r^d)(x - r^d)`,

which is `gapD d r z` here, and records in (M3) that `g_{d,r}` vanishes to second order at each
of the two contact densities `r` and `s_c(r)`, with a second derivative that is bounded above
and below, uniformly on compact sets of nonexceptional densities:

`g_{d,r}(z) = ½ g_{d,r}''(u) (z - u)² + O_{d,K}(|z - u|³)`,  `0 < c_{d,K} ≤ g_{d,r}''(u) ≤ C_{d,K}`.

## Contents

* `gapD`, `gapD1`, `gapD2` — the gap and its first two `z`-derivatives, with
  `hasDerivAt_gapD`, `hasDerivAt_gapD1` identifying them;
* `gapD_nonneg`, `gapD_eq_zero_iff` — nonnegativity and the two-point zero set `{r, s_c(r)}`,
  from the `supporting` and `contactSet_eq` content of (M2);
* `gapD1_contact`, `gapD2_contact` — `g'(u) = 0` and the paper's formula
  `g_{d,r}''(u) = h_{p_c(r),d}(u)/u` at a contact density `u`;
* `gapD2_contact_pos` — positivity of that second derivative, from `0 < h_{p_c(r),d}` at the
  Lubetzky–Zhao contacts (the contacts lie strictly inside the convex regions of
  `lem:convexity-defect`);
* `pow_mem_contacts` — the abscissa `r^d` is one of the two contacts of `p_c(r)`, the companion
  of `scGlobal_pow_mem`.

The uniform bounds, the Taylor expansion of (M3) and the density form of
`eq:contact-quadratic-separation` are in `LZBoundary/NonexceptionalGap.lean`.
-/

namespace UpperTailOptimizers

open Real Set

variable {d : ℕ}

/-- **The supporting cost gap** `g_{d,r}(z) = J_{p_c(r)}(z) - ℓ_r(z^d)` of
`eq:supporting-cost-gap`, in the density variable `z`. -/
noncomputable def gapD (d : ℕ) (r z : ℝ) : ℝ :=
  Jp (pcGlobal d r) z - (Jp (pcGlobal d r) r + slope d (pcGlobal d) r * (z ^ d - r ^ d))

/-- The first `z`-derivative of `g_{d,r}`. -/
noncomputable def gapD1 (d : ℕ) (r z : ℝ) : ℝ :=
  Jp' (pcGlobal d r) z - slope d (pcGlobal d) r * ((d : ℝ) * z ^ (d - 1))

/-- The second `z`-derivative of `g_{d,r}`. -/
noncomputable def gapD2 (d : ℕ) (r z : ℝ) : ℝ :=
  Jp'' z - slope d (pcGlobal d) r * ((d : ℝ) * ((d : ℝ) - 1) * z ^ (d - 2))

/-- On an arc, the global slope is the arc slope. -/
theorem slope_pcGlobal_eq (hd : 2 ≤ d) (M : LZBoundaryArc d) {r : ℝ} (hr : r ∈ M.U) :
    slope d (pcGlobal d) r = slope d M.pc r := by
  unfold slope
  rw [pcGlobal_eq_pc hd M hr]

/-- `g_{d,r}` in the `x = z^d` coordinate: it is the gap between `φ_{p_c(r),d}` and the
tangent line `ℓ_r` at `r^d`. -/
theorem gapD_eq_phi_sub (hd : 2 ≤ d) {r z : ℝ} (hr0 : 0 ≤ r) (hz0 : 0 ≤ z) :
    gapD d r z = phi (pcGlobal d r) d (z ^ d)
      - (phi (pcGlobal d r) d (r ^ d) + slope d (pcGlobal d) r * (z ^ d - r ^ d)) := by
  unfold gapD
  rw [Jp_eq_phi_pow hd hz0, Jp_eq_phi_pow hd hr0]

/-- `g_{d,r}(r) = 0`: the line touches at `r`. -/
@[simp] theorem gapD_self (d : ℕ) (r : ℝ) : gapD d r r = 0 := by
  unfold gapD; ring

/-- **The gap is nonnegative** on `[0,1]`: the supporting-line half of (M2). -/
theorem gapD_nonneg (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hexc : r ≠ rStar d)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ gapD d r z := by
  obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
  have h := M.supporting r hrU z hz
  unfold gapD
  rw [pcGlobal_eq_pc hd M hrU, slope_pcGlobal_eq hd M hrU]
  linarith

/-- **The zero set of the gap is the contact pair** `{r, s_c(r)}`: the equality half of (M2). -/
theorem gapD_eq_zero_iff (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hexc : r ≠ rStar d)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    gapD d r z = 0 ↔ z = r ∨ z = scGlobal d r := by
  obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
  have hset := M.contactSet_eq hd hrU
  have hmem : z ∈ contactSet d (M.pc r) r ↔ z = r ∨ z = M.sc r := by
    rw [hset]; simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [scGlobal_eq_sc hd M hrU, ← hmem]
  unfold contactSet gapD
  rw [pcGlobal_eq_pc hd M hrU, slope_pcGlobal_eq hd M hrU]
  simp only [Set.mem_ofPred_eq, slope]
  constructor
  · intro h; exact ⟨hz, by linarith⟩
  · intro h; linarith [h.2]

/-- `g_{d,r}` is differentiable in `z` on `(0,1)`, with derivative `gapD1`. -/
theorem hasDerivAt_gapD (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) : HasDerivAt (gapD d r) (gapD1 d r z) z := by
  obtain ⟨hp0, hple⟩ := pcGlobal_pos_le hd hr0 hr1
  have hp1 : pcGlobal d r < 1 := lt_of_le_of_lt hple (pStar_lt_one hd)
  have hJ := hasDerivAt_Jp (p := pcGlobal d r) hp0 hp1 hz0 hz1
  have hpow : HasDerivAt (fun y : ℝ => y ^ d) ((d : ℝ) * z ^ (d - 1)) z := hasDerivAt_pow d z
  have hlin : HasDerivAt
      (fun y : ℝ => Jp (pcGlobal d r) r + slope d (pcGlobal d) r * (y ^ d - r ^ d))
      (slope d (pcGlobal d) r * ((d : ℝ) * z ^ (d - 1))) z :=
    ((hpow.sub_const (r ^ d)).const_mul (slope d (pcGlobal d) r)).const_add
      (Jp (pcGlobal d r) r)
  exact hJ.sub hlin

/-- `gapD1` is differentiable in `z` on `(0,1)`, with derivative `gapD2`. -/
theorem hasDerivAt_gapD1 (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) : HasDerivAt (gapD1 d r) (gapD2 d r z) z := by
  obtain ⟨hp0, hple⟩ := pcGlobal_pos_le hd hr0 hr1
  have hp1 : pcGlobal d r < 1 := lt_of_le_of_lt hple (pStar_lt_one hd)
  have hJ := hasDerivAt_Jp' (p := pcGlobal d r) hp0 hp1 hz0 hz1
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have : (1 : ℕ) ≤ d := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hpow : HasDerivAt (fun y : ℝ => y ^ (d - 1)) (((d : ℝ) - 1) * z ^ (d - 2)) z := by
    have h := hasDerivAt_pow (d - 1) z
    rw [hcast] at h
    have hdd : d - 1 - 1 = d - 2 := by omega
    rwa [hdd] at h
  have hlin : HasDerivAt (fun y : ℝ => slope d (pcGlobal d) r * ((d : ℝ) * y ^ (d - 1)))
      (slope d (pcGlobal d) r * ((d : ℝ) * (((d : ℝ) - 1) * z ^ (d - 2)))) z :=
    (hpow.const_mul ((d : ℝ))).const_mul (slope d (pcGlobal d) r)
  have hkey := hJ.sub hlin
  have hrw : gapD2 d r z
      = Jp'' z - slope d (pcGlobal d) r * ((d : ℝ) * (((d : ℝ) - 1) * z ^ (d - 2))) := by
    unfold gapD2; ring
  rw [hrw]
  exact hkey

/-- **The abscissa `r^d` is a Lubetzky–Zhao contact of `p_c(r)`** — the companion of
`scGlobal_pow_mem`, obtained by reading the double tangent from its second contact. -/
theorem pow_mem_contacts (hd : 2 ≤ d) (G : GlobalContacts d) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hexc : r ≠ rStar d) :
    r ^ d = (G.ua (pcGlobal d r)) ^ d ∨ r ^ d = (G.ub (pcGlobal d r)) ^ d := by
  obtain ⟨M, hrU, -⟩ := lz_boundary_arcs hd hr0 hr1 hexc
  obtain ⟨hpc0, -, -, hscne, hsc0, hsc1⟩ := M.ordering r hrU
  obtain ⟨hmin, htouch⟩ := M.contact_data hd hrU
  rw [pcGlobal_eq_pc hd M hrU]
  -- the same line, based at the second contact
  have hmin' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      phi (M.pc r) d ((M.sc r) ^ d) + slope d M.pc r * (t - (M.sc r) ^ d) ≤ phi (M.pc r) d t := by
    intro t ht
    have h := hmin t ht
    have : phi (M.pc r) d ((M.sc r) ^ d) + slope d M.pc r * (t - (M.sc r) ^ d)
        = phi (M.pc r) d (r ^ d) + slope d M.pc r * (t - r ^ d) := by
      rw [← htouch]; ring
    rw [this]; exact h
  have htouch' : phi (M.pc r) d ((M.sc r) ^ d)
      + slope d M.pc r * (r ^ d - (M.sc r) ^ d) = phi (M.pc r) d (r ^ d) := by
    rw [← htouch]; ring
  have hne : (M.sc r) ^ d ≠ r ^ d := by
    intro hcon
    exact hscne ((pow_left_inj₀ hsc0.le hr0.le (by omega)).mp hcon)
  exact contact_mem_lz_boundary hd G hpc0 (M.pcLtPStar r hrU)
    ⟨pow_pos hsc0 d, pow_lt_one₀ hsc0.le hsc1 (by omega)⟩
    ⟨pow_pos hr0 d, pow_lt_one₀ hr0.le hr1 (by omega)⟩ hne hmin' htouch'

/-- **The convexity defect is positive at both contact densities.**  The contacts lie strictly
inside the two convex regions of `lem:convexity-defect`, so `0 < h_{p_c(r),d}` there. -/
theorem hpd_pos_contacts (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hexc : r ≠ rStar d)
    {u : ℝ} (hu : u = r ∨ u = scGlobal d r) : 0 < hpd (pcGlobal d r) d u := by
  obtain ⟨G⟩ := exists_globalContacts hd
  obtain ⟨hp0, -⟩ := pcGlobal_pos_le hd hr0 hr1
  have hp := pcGlobal_lt_pStar hd hr0 hr1 hexc
  obtain ⟨hua0, huas, hubs, hub1, -, hHa, hHb⟩ := G.contact (pcGlobal d r) hp0 hp
  have hub0 : 0 < G.ub (pcGlobal d r) := lt_trans (rStar_pos hd) hubs
  obtain ⟨hsc0, hsc1⟩ := scGlobal_mem_Ioo hd hr0 hr1
  have key : ∀ y : ℝ, 0 < y →
      (y ^ d = (G.ua (pcGlobal d r)) ^ d ∨ y ^ d = (G.ub (pcGlobal d r)) ^ d) →
      0 < hpd (pcGlobal d r) d y := by
    intro y hy0 hmem
    rcases hmem with h | h
    · have : y = G.ua (pcGlobal d r) := (pow_left_inj₀ hy0.le hua0.le (by omega)).mp h
      rw [this]; exact hHa
    · have : y = G.ub (pcGlobal d r) := (pow_left_inj₀ hy0.le hub0.le (by omega)).mp h
      rw [this]; exact hHb
  rcases hu with h | h
  · rw [h]; exact key r hr0 (pow_mem_contacts hd G hr0 hr1 hexc)
  · rw [h]; exact key _ hsc0 (scGlobal_pow_mem hd G hr0 hr1 hexc)

/-- **The gap has a vanishing derivative at each contact density.**  At `u = r` this is the
definition of the slope; at `u = s_c(r)` it is the interior minimum of a nonnegative gap. -/
theorem gapD1_contact (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hexc : r ≠ rStar d)
    {u : ℝ} (hu : u = r ∨ u = scGlobal d r) : gapD1 d r u = 0 := by
  obtain ⟨hsc0, hsc1⟩ := scGlobal_mem_Ioo hd hr0 hr1
  rcases hu with h | h
  · rw [h]
    have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (dpos hd)
    have hrne : r ^ (d - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hr0)
    unfold gapD1 slope
    field_simp
    ring
  · rw [h]
    -- interior minimum of the nonnegative gap
    have hzero : gapD d r (scGlobal d r) = 0 :=
      (gapD_eq_zero_iff hd hr0 hr1 hexc ⟨hsc0.le, hsc1.le⟩).mpr (Or.inr rfl)
    have hmin : IsLocalMin (gapD d r) (scGlobal d r) := by
      filter_upwards [Ioo_mem_nhds hsc0 hsc1] with z hz
      rw [hzero]
      exact gapD_nonneg hd hr0 hr1 hexc (Set.Ioo_subset_Icc_self hz)
    exact hmin.hasDerivAt_eq_zero (hasDerivAt_gapD hd hr0 hr1 hsc0 hsc1)

/-- **The paper's formula for the curvature at a contact**, from (M3):
`g_{d,r}''(u) = h_{p_c(r),d}(u)/u`. -/
theorem gapD2_contact (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hexc : r ≠ rStar d)
    {u : ℝ} (hu : u = r ∨ u = scGlobal d r) (hu0 : 0 < u) :
    gapD2 d r u = hpd (pcGlobal d r) d u / u := by
  have h1 : gapD1 d r u = 0 := gapD1_contact hd hr0 hr1 hexc hu
  have hune : u ≠ 0 := ne_of_gt hu0
  have hpow : u ^ (d - 2) * u = u ^ (d - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  have hJp' : Jp' (pcGlobal d r) u = slope d (pcGlobal d) r * ((d : ℝ) * u ^ (d - 1)) := by
    unfold gapD1 at h1; linarith
  unfold gapD2 hpd
  rw [hJp', ← hpow]
  field_simp

/-- **The curvature at a contact is positive.** -/
theorem gapD2_contact_pos (hd : 2 ≤ d) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hexc : r ≠ rStar d)
    {u : ℝ} (hu : u = r ∨ u = scGlobal d r) (hu0 : 0 < u) : 0 < gapD2 d r u := by
  rw [gapD2_contact hd hr0 hr1 hexc hu hu0]
  exact div_pos (hpd_pos_contacts hd hr0 hr1 hexc hu) hu0

end UpperTailOptimizers
