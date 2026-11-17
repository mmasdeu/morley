import M5Base
import M2P
open XamboMorley
open XamboMorley.OrientedTriangle
open Function Set
set_option maxHeartbeats 2000000

/-! ### The green/blue incidence certificates of the nine guide lines (`M4GBCert`)

`smwh1zs5u/m4/M4Guide.lean` reduces `IsGuideLine (m4L s d)` to two named
obligations, `M4GBCert` (the four green/blue incidences of each of the nine lines)
and `M4Excl` (no further point on the line).  This file discharges `M4GBCert`
completely, from the 54 compiled incidences of `M2P.lean`:

* green: for every `(s,d)` the two green points `m4Six` prescribes are literally the
  points whose incidence `M2P.m2_par_ijk` records;
* blue: `M2P.m2_parB_ijk` records the incidence of the blue point with the *green*
  join through the same two green points; since `m4L s d` contains those two green
  points and two distinct points determine a line, the blue point lies on `m4L s d`.

No new axiom, no `sorry`; the only inputs are root and `M2P`. -/

namespace XamboMorley
namespace M4
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! #### Helpers -/

/-- Membership in the line through `P` in direction `Q - P`, from the standard
parallelism shape produced by the `M2P` incidences. -/
theorem m5_mem_of_par {X P Q : E} {ℓ : Line E} (hbase : ℓ.base = P)
    (hdir : ℓ.direction = Q - P) (hPQ : P ≠ Q)
    (h : Parallel (X - P) (P - Q)) : ℓ.mem X := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hr
    exact hPQ (sub_eq_zero.mp (by simpa using hr))
  rw [Line.mem_iff_parallel, hbase, hdir]
  refine ⟨-r⁻¹, ?_⟩
  have h2 : r • (X - P) = -(Q - P) := by rw [← hr]; abel
  calc X - P = r⁻¹ • (r • (X - P)) := by rw [smul_smul, inv_mul_cancel₀ hr0, one_smul]
    _ = r⁻¹ • (-(Q - P)) := by rw [h2]
    _ = (-r⁻¹) • (Q - P) := by rw [smul_neg, neg_smul]

/-- If a line contains two distinct points `G1`, `G2`, then any point `X` with
`X - G1` parallel to `G1 - G2` lies on it. -/
theorem m5_mem_of_two_mem {G1 G2 X : E} {ℓ : Line E} (hG12 : G1 ≠ G2)
    (h1 : ℓ.mem G1) (h2 : ℓ.mem G2) (hpar : Parallel (X - G1) (G1 - G2)) : ℓ.mem X := by
  have hne : G2 - G1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hG12)
  let L' : Line E := ⟨G1, G2 - G1, hne⟩
  have hL' : L'.mem X := m5_mem_of_par (ℓ := L') rfl rfl hG12 hpar
  have hmem2 : L'.mem G2 := by
    rw [Line.mem_iff_parallel]
    exact ⟨1, by rw [one_smul]⟩
  exact ((m4_mem_iff_of_two_mem hG12 h1 h2 (Line.mem_base L') hmem2 X).mpr hL')

/-! #### The 36 concrete incidences -/

theorem m5_g1_00 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (0 : TrisectorLabel) - m4Lp (0 : TrisectorLabel) (0 : TrisectorLabel), (0 : TrisectorLabel) + m4Lp (0 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_p T h (0 : TrisectorLabel) (0 : TrisectorLabel)) (m4L_mem_q T h (0 : TrisectorLabel) (0 : TrisectorLabel)) (m2_par_000 T h)

theorem m5_g2_00 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (0 : TrisectorLabel) - m4Lq (0 : TrisectorLabel) (0 : TrisectorLabel), (0 : TrisectorLabel) + m4Lq (0 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_q T h (0 : TrisectorLabel) (0 : TrisectorLabel)) (m4L_mem_p T h (0 : TrisectorLabel) (0 : TrisectorLabel)) (m2_par_212 T h)

theorem m5_b1_00 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (0 : TrisectorLabel) - (0 : TrisectorLabel) - 1 - m4Lp (0 : TrisectorLabel) (0 : TrisectorLabel), m4Lp (0 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g2_00 T h) (m5_g1_00 T h) (m2_parB_120 T h)

theorem m5_b2_00 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (0 : TrisectorLabel) - (0 : TrisectorLabel) - 1 - m4Lq (0 : TrisectorLabel) (0 : TrisectorLabel), m4Lq (0 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g1_00 T h) (m5_g2_00 T h) (m2_parB_002 T h)

theorem m5_g1_01 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (0 : TrisectorLabel) - m4Lp (0 : TrisectorLabel) (1 : TrisectorLabel), (1 : TrisectorLabel) + m4Lp (0 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_p T h (0 : TrisectorLabel) (1 : TrisectorLabel)) (m4L_mem_q T h (0 : TrisectorLabel) (1 : TrisectorLabel)) (m2_par_122 T h)

theorem m5_g2_01 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (0 : TrisectorLabel) - m4Lq (0 : TrisectorLabel) (1 : TrisectorLabel), (1 : TrisectorLabel) + m4Lq (0 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_q T h (0 : TrisectorLabel) (1 : TrisectorLabel)) (m4L_mem_p T h (0 : TrisectorLabel) (1 : TrisectorLabel)) (m2_par_210 T h)

theorem m5_b1_01 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (0 : TrisectorLabel) - (1 : TrisectorLabel) - 1 - m4Lp (0 : TrisectorLabel) (1 : TrisectorLabel), m4Lp (0 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g2_01 T h) (m5_g1_01 T h) (m2_parB_101 T h)

theorem m5_b2_01 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (0 : TrisectorLabel) - (1 : TrisectorLabel) - 1 - m4Lq (0 : TrisectorLabel) (1 : TrisectorLabel), m4Lq (0 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g1_01 T h) (m5_g2_01 T h) (m2_parB_222 T h)

theorem m5_g1_02 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (0 : TrisectorLabel) - m4Lp (0 : TrisectorLabel) (2 : TrisectorLabel), (2 : TrisectorLabel) + m4Lp (0 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_p T h (0 : TrisectorLabel) (2 : TrisectorLabel)) (m4L_mem_q T h (0 : TrisectorLabel) (2 : TrisectorLabel)) (m2_par_002 T h)

theorem m5_g2_02 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (0 : TrisectorLabel) - m4Lq (0 : TrisectorLabel) (2 : TrisectorLabel), (2 : TrisectorLabel) + m4Lq (0 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_q T h (0 : TrisectorLabel) (2 : TrisectorLabel)) (m4L_mem_p T h (0 : TrisectorLabel) (2 : TrisectorLabel)) (m2_par_120 T h)

theorem m5_b1_02 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (0 : TrisectorLabel) - (2 : TrisectorLabel) - 1 - m4Lp (0 : TrisectorLabel) (2 : TrisectorLabel), m4Lp (0 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g2_02 T h) (m5_g1_02 T h) (m2_parB_200 T h)

theorem m5_b2_02 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (0 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (0 : TrisectorLabel) - (2 : TrisectorLabel) - 1 - m4Lq (0 : TrisectorLabel) (2 : TrisectorLabel), m4Lq (0 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g1_02 T h) (m5_g2_02 T h) (m2_parB_021 T h)

theorem m5_g1_10 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (1 : TrisectorLabel) - m4Lp (1 : TrisectorLabel) (0 : TrisectorLabel), (0 : TrisectorLabel) + m4Lp (1 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_p T h (1 : TrisectorLabel) (0 : TrisectorLabel)) (m4L_mem_q T h (1 : TrisectorLabel) (0 : TrisectorLabel)) (m2_par_101 T h)

theorem m5_g2_10 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (1 : TrisectorLabel) - m4Lq (1 : TrisectorLabel) (0 : TrisectorLabel), (0 : TrisectorLabel) + m4Lq (1 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_q T h (1 : TrisectorLabel) (0 : TrisectorLabel)) (m4L_mem_p T h (1 : TrisectorLabel) (0 : TrisectorLabel)) (m2_par_222 T h)

theorem m5_b1_10 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (1 : TrisectorLabel) - (0 : TrisectorLabel) - 1 - m4Lp (1 : TrisectorLabel) (0 : TrisectorLabel), m4Lp (1 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g2_10 T h) (m5_g1_10 T h) (m2_parB_221 T h)

theorem m5_b2_10 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (1 : TrisectorLabel) - (0 : TrisectorLabel) - 1 - m4Lq (1 : TrisectorLabel) (0 : TrisectorLabel), m4Lq (1 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g1_10 T h) (m5_g2_10 T h) (m2_parB_012 T h)

theorem m5_g1_11 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (1 : TrisectorLabel) - m4Lp (1 : TrisectorLabel) (1 : TrisectorLabel), (1 : TrisectorLabel) + m4Lp (1 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_p T h (1 : TrisectorLabel) (1 : TrisectorLabel)) (m4L_mem_q T h (1 : TrisectorLabel) (1 : TrisectorLabel)) (m2_par_102 T h)

theorem m5_g2_11 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (1 : TrisectorLabel) - m4Lq (1 : TrisectorLabel) (1 : TrisectorLabel), (1 : TrisectorLabel) + m4Lq (1 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_q T h (1 : TrisectorLabel) (1 : TrisectorLabel)) (m4L_mem_p T h (1 : TrisectorLabel) (1 : TrisectorLabel)) (m2_par_011 T h)

theorem m5_b1_11 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (1 : TrisectorLabel) - (1 : TrisectorLabel) - 1 - m4Lp (1 : TrisectorLabel) (1 : TrisectorLabel), m4Lp (1 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g2_11 T h) (m5_g1_11 T h) (m2_parB_111 T h)

theorem m5_b2_11 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (1 : TrisectorLabel) - (1 : TrisectorLabel) - 1 - m4Lq (1 : TrisectorLabel) (1 : TrisectorLabel), m4Lq (1 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g1_11 T h) (m5_g2_11 T h) (m2_parB_020 T h)

theorem m5_g1_12 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (1 : TrisectorLabel) - m4Lp (1 : TrisectorLabel) (2 : TrisectorLabel), (2 : TrisectorLabel) + m4Lp (1 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_p T h (1 : TrisectorLabel) (2 : TrisectorLabel)) (m4L_mem_q T h (1 : TrisectorLabel) (2 : TrisectorLabel)) (m2_par_221 T h)

theorem m5_g2_12 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (1 : TrisectorLabel) - m4Lq (1 : TrisectorLabel) (2 : TrisectorLabel), (2 : TrisectorLabel) + m4Lq (1 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_q T h (1 : TrisectorLabel) (2 : TrisectorLabel)) (m4L_mem_p T h (1 : TrisectorLabel) (2 : TrisectorLabel)) (m2_par_012 T h)

theorem m5_b1_12 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (1 : TrisectorLabel) - (2 : TrisectorLabel) - 1 - m4Lp (1 : TrisectorLabel) (2 : TrisectorLabel), m4Lp (1 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (2 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g2_12 T h) (m5_g1_12 T h) (m2_parB_122 T h)

theorem m5_b2_12 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (1 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (1 : TrisectorLabel) - (2 : TrisectorLabel) - 1 - m4Lq (1 : TrisectorLabel) (2 : TrisectorLabel), m4Lq (1 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g1_12 T h) (m5_g2_12 T h) (m2_parB_210 T h)

theorem m5_g1_20 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (2 : TrisectorLabel) - m4Lp (2 : TrisectorLabel) (0 : TrisectorLabel), (0 : TrisectorLabel) + m4Lp (2 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_p T h (2 : TrisectorLabel) (0 : TrisectorLabel)) (m4L_mem_q T h (2 : TrisectorLabel) (0 : TrisectorLabel)) (m2_par_020 T h)

theorem m5_g2_20 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (2 : TrisectorLabel) - m4Lq (2 : TrisectorLabel) (0 : TrisectorLabel), (0 : TrisectorLabel) + m4Lq (2 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_q T h (2 : TrisectorLabel) (0 : TrisectorLabel)) (m4L_mem_p T h (2 : TrisectorLabel) (0 : TrisectorLabel)) (m2_par_111 T h)

theorem m5_b1_20 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (2 : TrisectorLabel) - (0 : TrisectorLabel) - 1 - m4Lp (2 : TrisectorLabel) (0 : TrisectorLabel), m4Lp (2 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g2_20 T h) (m5_g1_20 T h) (m2_parB_110 T h)

theorem m5_b2_20 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (0 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (2 : TrisectorLabel) - (0 : TrisectorLabel) - 1 - m4Lq (2 : TrisectorLabel) (0 : TrisectorLabel), m4Lq (2 : TrisectorLabel) (0 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g1_20 T h) (m5_g2_20 T h) (m2_parB_201 T h)

theorem m5_g1_21 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (2 : TrisectorLabel) - m4Lp (2 : TrisectorLabel) (1 : TrisectorLabel), (1 : TrisectorLabel) + m4Lp (2 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_p T h (2 : TrisectorLabel) (1 : TrisectorLabel)) (m4L_mem_q T h (2 : TrisectorLabel) (1 : TrisectorLabel)) (m2_par_200 T h)

theorem m5_g2_21 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (2 : TrisectorLabel) - m4Lq (2 : TrisectorLabel) (1 : TrisectorLabel), (1 : TrisectorLabel) + m4Lq (2 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_q T h (2 : TrisectorLabel) (1 : TrisectorLabel)) (m4L_mem_p T h (2 : TrisectorLabel) (1 : TrisectorLabel)) (m2_par_021 T h)

theorem m5_b1_21 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (2 : TrisectorLabel) - (1 : TrisectorLabel) - 1 - m4Lp (2 : TrisectorLabel) (1 : TrisectorLabel), m4Lp (2 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (1 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g2_21 T h) (m5_g1_21 T h) (m2_parB_212 T h)

theorem m5_b2_21 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (1 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (2 : TrisectorLabel) - (1 : TrisectorLabel) - 1 - m4Lq (2 : TrisectorLabel) (1 : TrisectorLabel), m4Lq (2 : TrisectorLabel) (1 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (2 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (0 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g1_21 T h) (m5_g2_21 T h) (m2_parB_000 T h)

theorem m5_g1_22 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (2 : TrisectorLabel) - m4Lp (2 : TrisectorLabel) (2 : TrisectorLabel), (2 : TrisectorLabel) + m4Lp (2 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_p T h (2 : TrisectorLabel) (2 : TrisectorLabel)) (m4L_mem_q T h (2 : TrisectorLabel) (2 : TrisectorLabel)) (m2_par_201 T h)

theorem m5_g2_22 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.green, (2 : TrisectorLabel) - m4Lq (2 : TrisectorLabel) (2 : TrisectorLabel), (2 : TrisectorLabel) + m4Lq (2 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.red, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.red, (2 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m4L_mem_q T h (2 : TrisectorLabel) (2 : TrisectorLabel)) (m4L_mem_p T h (2 : TrisectorLabel) (2 : TrisectorLabel)) (m2_par_110 T h)

theorem m5_b1_22 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (2 : TrisectorLabel) - (2 : TrisectorLabel) - 1 - m4Lp (2 : TrisectorLabel) (2 : TrisectorLabel), m4Lp (2 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (0 : TrisectorLabel), (2 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g2_22 T h) (m5_g1_22 T h) (m2_parB_102 T h)

theorem m5_b2_22 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m4L T h (2 : TrisectorLabel) (2 : TrisectorLabel)).mem
      (T.constellationPoint ⟨.blue, (2 : TrisectorLabel) - (2 : TrisectorLabel) - 1 - m4Lq (2 : TrisectorLabel) (2 : TrisectorLabel), m4Lq (2 : TrisectorLabel) (2 : TrisectorLabel)⟩) := by
  refine m5_mem_of_two_mem (G1 := T.constellationPoint ⟨.green, (0 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (G2 := T.constellationPoint ⟨.green, (1 : TrisectorLabel), (0 : TrisectorLabel)⟩)
    (X := T.constellationPoint ⟨.blue, (1 : TrisectorLabel), (1 : TrisectorLabel)⟩)
    (m2_cp_ne_same T h (by decide)) (m5_g1_22 T h) (m5_g2_22 T h) (m2_parB_011 T h)


/-! #### The four incidence families, uniformly in `(s,d)` -/

theorem m5_gbc_green_p (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) :
    (m4L T h s d).mem (T.constellationPoint ⟨.green, s - m4Lp s d, d + m4Lp s d⟩) := by
  rcases zmod3_cases s with rfl | rfl | rfl <;> rcases zmod3_cases d with rfl | rfl | rfl
  · exact m5_g1_00 T h
  · exact m5_g1_01 T h
  · exact m5_g1_02 T h
  · exact m5_g1_10 T h
  · exact m5_g1_11 T h
  · exact m5_g1_12 T h
  · exact m5_g1_20 T h
  · exact m5_g1_21 T h
  · exact m5_g1_22 T h

theorem m5_gbc_green_q (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) :
    (m4L T h s d).mem (T.constellationPoint ⟨.green, s - m4Lq s d, d + m4Lq s d⟩) := by
  rcases zmod3_cases s with rfl | rfl | rfl <;> rcases zmod3_cases d with rfl | rfl | rfl
  · exact m5_g2_00 T h
  · exact m5_g2_01 T h
  · exact m5_g2_02 T h
  · exact m5_g2_10 T h
  · exact m5_g2_11 T h
  · exact m5_g2_12 T h
  · exact m5_g2_20 T h
  · exact m5_g2_21 T h
  · exact m5_g2_22 T h

theorem m5_gbc_blue_p (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) :
    (m4L T h s d).mem
      (T.constellationPoint ⟨.blue, s - d - 1 - m4Lp s d, m4Lp s d⟩) := by
  rcases zmod3_cases s with rfl | rfl | rfl <;> rcases zmod3_cases d with rfl | rfl | rfl
  · exact m5_b1_00 T h
  · exact m5_b1_01 T h
  · exact m5_b1_02 T h
  · exact m5_b1_10 T h
  · exact m5_b1_11 T h
  · exact m5_b1_12 T h
  · exact m5_b1_20 T h
  · exact m5_b1_21 T h
  · exact m5_b1_22 T h

theorem m5_gbc_blue_q (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) :
    (m4L T h s d).mem
      (T.constellationPoint ⟨.blue, s - d - 1 - m4Lq s d, m4Lq s d⟩) := by
  rcases zmod3_cases s with rfl | rfl | rfl <;> rcases zmod3_cases d with rfl | rfl | rfl
  · exact m5_b2_00 T h
  · exact m5_b2_01 T h
  · exact m5_b2_02 T h
  · exact m5_b2_10 T h
  · exact m5_b2_11 T h
  · exact m5_b2_12 T h
  · exact m5_b2_20 T h
  · exact m5_b2_21 T h
  · exact m5_b2_22 T h

/-! #### Reading off membership in `m4Six` -/

theorem m4Six_green_elim (s d f g : TrisectorLabel)
    (hmem : (⟨.green, f, g⟩ : ConstellationIndex) ∈ m4Six s d) :
    (f = s - m4Lp s d ∧ g = d + m4Lp s d) ∨ (f = s - m4Lq s d ∧ g = d + m4Lq s d) := by
  unfold m4Six at hmem
  rcases Finset.mem_insert.mp hmem with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by decide : TrisectorColor.green ≠ TrisectorColor.red)
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by decide : TrisectorColor.green ≠ TrisectorColor.red)
  rcases Finset.mem_insert.mp h with h | h
  · injection h with _ h2 h3
    exact Or.inl ⟨h2, h3⟩
  rcases Finset.mem_insert.mp h with h | h
  · injection h with _ h2 h3
    exact Or.inr ⟨h2, h3⟩
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by decide : TrisectorColor.green ≠ TrisectorColor.blue)
  rw [Finset.mem_singleton] at h
  exact absurd (congrArg ConstellationIndex.color h) (by decide : TrisectorColor.green ≠ TrisectorColor.blue)

theorem m4Six_blue_elim (s d f g : TrisectorLabel)
    (hmem : (⟨.blue, f, g⟩ : ConstellationIndex) ∈ m4Six s d) :
    (f = s - d - 1 - m4Lp s d ∧ g = m4Lp s d) ∨
      (f = s - d - 1 - m4Lq s d ∧ g = m4Lq s d) := by
  unfold m4Six at hmem
  rcases Finset.mem_insert.mp hmem with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by decide : TrisectorColor.blue ≠ TrisectorColor.red)
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by decide : TrisectorColor.blue ≠ TrisectorColor.red)
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by decide : TrisectorColor.blue ≠ TrisectorColor.green)
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by decide : TrisectorColor.blue ≠ TrisectorColor.green)
  rcases Finset.mem_insert.mp h with h | h
  · injection h with _ h2 h3
    exact Or.inl ⟨h2, h3⟩
  rw [Finset.mem_singleton] at h
  injection h with _ h2 h3
  exact Or.inr ⟨h2, h3⟩

/-! #### `M4GBCert` -/

/-- **The green/blue incidence certificates of all nine guide lines.**  This is the
`M4GBCert` obligation of `M4Guide.lean §4`, discharged from the compiled incidences of
`M2P.lean`. -/
theorem m5_M4GBCert (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) : M4GBCert T h s d := by
  intro q hq hc
  obtain ⟨c, f, g⟩ := q
  cases c with
  | red => exact absurd rfl hc
  | green =>
      rcases m4Six_green_elim s d f g hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact m5_gbc_green_p T h s d
      · exact m5_gbc_green_q T h s d
  | blue =>
      rcases m4Six_blue_elim s d f g hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact m5_gbc_blue_p T h s d
      · exact m5_gbc_blue_q T h s d


/-- **Guide-line membership from the exclusion alone.**  With `M4GBCert` discharged,
`IsGuideLine (m4L s d)` now depends only on `M4Excl` (no constellation point outside
`m4Six s d` lies on the line). -/
theorem m5_isGuideLine_of_excl (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) (hex : M4Excl T h s d) : T.IsGuideLine (m4L T h s d) :=
  m4IsGuideLine_of_certs T h s d (m5_M4GBCert T h s d) hex

end M4
end XamboMorley

#print axioms XamboMorley.M4.m5_M4GBCert
#print axioms XamboMorley.M4.m5_isGuideLine_of_excl
