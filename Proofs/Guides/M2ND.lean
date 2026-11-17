/-
  member m2, swarm smwha0atu, direction d8: NON-DIAGONAL EXCLUSIONS / NO THIRD POINT.

  Proves, unconditionally and for *every* oriented triangle, the non-diagonal exclusion
  hypothesis `m3HPnd` of `smwh7aexl/m3/M3G.lean`:

    two distinct same-colour constellation points with different label sums and
    different label differences never have a join parallel to a Morley side.

  Why this is exactly the non-diagonal family: for labels `p ≠ q` in `ZMod 3 × ZMod 3`
  the conditions "different label sums" (`p.1+p.2 ≠ q.1+q.2`) and "different label
  differences" (`¬ m3Diag p q`) together force `p.1 = q.1` or `p.2 = q.2`
  (`m2_pair_row_or_col`).  Such a pair lies on one trisector through a vertex
  (`redB i`, `redC j`, `greenC i`, `greenA j`, `blueA i`, `blueB j`), so the join of the
  pair is that trisector.  Hence `m3HPnd` is precisely the statement that *no trisector of
  the triangle is parallel to a Morley side*: 3 colours times 2 trisectors times 3 side
  directions.  All 18 cases are proved here from the root's exact side forms
  (`Y_sub_X`, `Z_sub_Y`, `X_sub_Z`), the root's trisector directions (`m6_*_dir`), the
  rotation relations `bStar_relation` / `aStar_relation`, and one elementary arithmetic
  fact: `sin (x + m·π/3) ≠ 0` for `0 < x < π/3` and every integer `m`.

  Consequences (all axiom-clean, compiled in `M2ND2.lean`):
  * `9 ≤ T.guideLines.ncard` unconditionally (the constructive lower bound of
    `guideLines_card`, which previously needed `m3HPnd` as a hypothesis);
  * "no third point of a colour on a side-parallel line" (`m3_no_third_nd`) and
    "exactly two points of a colour on it" (`m3_colour_two_nd`), unconditionally.
-/
import M3G
import M3H

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set

namespace XamboMorley
namespace OrientedTriangle

open XamboMorley.OrientedTriangle.OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! ## 1. The elementary arithmetic fact

`0 < x < π/3` and `m : ℤ` give `sin (x + m π/3) ≠ 0`: the open interval between two
consecutive multiples of `π/3` never contains a multiple of `π`. -/

theorem m2_sin_third_add_ne (x : ℝ) (m : ℤ) (h0 : 0 < x) (h1 : x < Real.pi / 3) :
    Real.sin (x + (m : ℝ) * (Real.pi / 3)) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  have hx : x = (n : ℝ) * Real.pi - (m : ℝ) * (Real.pi / 3) := by linarith
  have h3 : 3 * x = ((3 * n - m : ℤ) : ℝ) * Real.pi := by
    rw [hx]; push_cast; ring
  have hk0 : (0 : ℤ) < 3 * n - m := by
    have hp : (0 : ℝ) < Real.pi := Real.pi_pos
    have : (0 : ℝ) < ((3 * n - m : ℤ) : ℝ) * Real.pi := by rw [← h3]; linarith
    have h2 : (0 : ℝ) < ((3 * n - m : ℤ) : ℝ) := by nlinarith
    exact_mod_cast h2
  have hk1 : 3 * n - m < 1 := by
    have hp : (0 : ℝ) < Real.pi := Real.pi_pos
    have hlt : ((3 * n - m : ℤ) : ℝ) * Real.pi < 1 * Real.pi := by
      rw [← h3, one_mul]; linarith
    have h2 : ((3 * n - m : ℤ) : ℝ) < 1 :=
      lt_of_mul_lt_mul_right hlt (le_of_lt hp)
    exact_mod_cast h2
  omega

theorem m2_sin_neg_third_add_ne (x : ℝ) (m : ℤ) (h0 : 0 < x) (h1 : x < Real.pi / 3) :
    Real.sin (-x + (m : ℝ) * (Real.pi / 3)) ≠ 0 := by
  have h := m2_sin_third_add_ne x (-m) h0 h1
  have he : -x + (m : ℝ) * (Real.pi / 3)
      = -(x + ((-m : ℤ) : ℝ) * (Real.pi / 3)) := by push_cast; ring
  rw [he, Real.sin_neg]
  exact neg_ne_zero.mpr h

/-! ## 2. Rotation algebra: the trisector directions all as rotations of `aStar` -/

theorem m2_rot_neg (u : E) (t : ℝ) :
    rotateVector o (-u) t = -rotateVector o u t := by
  rw [show -u = (-1 : ℝ) • u by simp, rotateVector_smul, neg_one_smul]

theorem m2_rot_congr (u : E) {a b : ℝ} (h : a = b) :
    rotateVector o u a = rotateVector o u b := by rw [h]

theorem m2_neg_rot (u : E) (θ : ℝ) :
    -rotateVector o u θ = rotateVector o u (θ + Real.pi) := by
  rw [← m1_rotateVector_pi (o := o) (v := rotateVector o u θ), ← rotateVector_add_angle]
  exact m2_rot_congr _ (by ring)

theorem m2_rot_bStar (T : OrientedTriangle E o) (t : ℝ) :
    rotateVector o T.bStar t = rotateVector o T.aStar (Real.pi - 3 * T.gamma + t) := by
  rw [bStar_relation, m2_rot_neg, m2_neg_rot, ← rotateVector_add_angle]
  exact m2_rot_congr _ (by ring)

theorem m2_cStar_eq (T : OrientedTriangle E o) :
    T.cStar = rotateVector o T.aStar (3 * T.beta - Real.pi) := by
  have h : T.aStar = rotateVector o T.cStar (Real.pi - 3 * T.beta) := by
    rw [aStar_relation, m2_neg_rot]
    exact m2_rot_congr _ (by ring)
  have h2 := congrArg (fun v : E => rotateVector o v (3 * T.beta - Real.pi)) h
  rw [← rotateVector_add_angle,
    show 3 * T.beta - Real.pi + (Real.pi - 3 * T.beta) = 0 by ring,
    rotateVector_zero_angle] at h2
  exact h2.symm

theorem m2_rot_cStar (T : OrientedTriangle E o) (t : ℝ) :
    rotateVector o T.cStar t = rotateVector o T.aStar (3 * T.beta - Real.pi + t) := by
  rw [m2_cStar_eq, ← rotateVector_add_angle]
  exact m2_rot_congr _ (by ring)

/-! ## 3. The three Morley sides as rotations of `aStar` -/

theorem m2_side0_rot (T : OrientedTriangle E o) :
    T.Y - T.X = (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) •
      rotateVector o T.aStar (T.alpha + 2 * T.beta) :=
  Y_sub_X T

theorem m2_side1_rot (T : OrientedTriangle E o) :
    T.Z - T.Y = (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) •
      rotateVector o T.aStar (Real.pi + T.beta - T.gamma) := by
  rw [Z_sub_Y, m2_rot_bStar]
  congr 1
  ring

theorem m2_side2_rot (T : OrientedTriangle E o) :
    T.X - T.Z = (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) •
      rotateVector o T.aStar (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi) := by
  rw [X_sub_Z, m2_rot_cStar]
  congr 1
  ring

/-! ## 4. The six trisector directions as scaled rotations of `aStar` -/

theorem m2_redB_rot (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (T.redB i).direction
      = T.aLength • rotateVector o T.aStar (T.beta + labelAngle i) := by
  rw [m6_redB_dir, show T.C - T.B = T.aLength • T.aStar from T.a_eq, rotateVector_smul]

theorem m2_redC_rot (T : OrientedTriangle E o) (j : TrisectorLabel) :
    (T.redC j).direction
      = T.bLength • rotateVector o T.aStar (Real.pi - T.gamma - labelAngle j) := by
  rw [m6_redC_dir, show T.A - T.C = T.bLength • T.bStar from T.b_eq, rotateVector_smul,
    m2_rot_bStar]
  congr 1
  ring

theorem m2_greenC_rot (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (T.greenC i).direction
      = T.bLength • rotateVector o T.aStar (Real.pi - 2 * T.gamma + labelAngle i) := by
  rw [m6_greenC_dir, show T.A - T.C = T.bLength • T.bStar from T.b_eq, rotateVector_smul,
    m2_rot_bStar]
  congr 1
  ring

theorem m2_greenA_rot (T : OrientedTriangle E o) (j : TrisectorLabel) :
    (T.greenA j).direction
      = T.cLength • rotateVector o T.aStar (2 * T.alpha + 3 * T.beta - Real.pi
          - labelAngle j) := by
  rw [m6_greenA_dir, show T.B - T.A = T.cLength • T.cStar from T.c_eq, rotateVector_smul,
    m2_rot_cStar]
  congr 1
  ring

theorem m2_blueA_rot (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (T.blueA i).direction
      = T.cLength • rotateVector o T.aStar (T.alpha + 3 * T.beta - Real.pi
          + labelAngle i) := by
  rw [m6_blueA_dir, show T.B - T.A = T.cLength • T.cStar from T.c_eq, rotateVector_smul,
    m2_rot_cStar]
  congr 1
  ring

theorem m2_blueB_rot (T : OrientedTriangle E o) (j : TrisectorLabel) :
    (T.blueB j).direction
      = T.aLength • rotateVector o T.aStar (2 * T.beta - labelAngle j) := by
  rw [m6_blueB_dir, show T.C - T.B = T.aLength • T.aStar from T.a_eq, rotateVector_smul]

/-! ## 5. The eighteen angle differences

Each is `±x + m·(π/3)` with `x ∈ {α, β, γ}` and an explicit integer `m`. -/

theorem m2_gamma_lt (T : OrientedTriangle E o) : T.gamma < Real.pi / 3 := by
  have := m3_three_gamma_lt_pi T; linarith

theorem m2_alpha_lt (T : OrientedTriangle E o) : T.alpha < Real.pi / 3 := by
  have := m3_three_alpha_lt_pi T; linarith

theorem m2_beta_lt (T : OrientedTriangle E o) : T.beta < Real.pi / 3 := by
  have := m3_three_beta_lt_pi T; linarith

/-- `redB i` against `Y - X`. -/
theorem m2_sin_redB_0 (T : OrientedTriangle E o) (i : TrisectorLabel) :
    Real.sin (T.beta + labelAngle i - (T.alpha + 2 * T.beta)) ≠ 0 := by
  have he : T.beta + labelAngle i - (T.alpha + 2 * T.beta)
      = T.gamma + ((2 * (i.val : ℤ) - 1 : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_third_add_ne T.gamma _ (m3_gamma_pos T) (m2_gamma_lt T)

/-- `redB i` against `Z - Y`. -/
theorem m2_sin_redB_1 (T : OrientedTriangle E o) (i : TrisectorLabel) :
    Real.sin (T.beta + labelAngle i - (Real.pi + T.beta - T.gamma)) ≠ 0 := by
  have he : T.beta + labelAngle i - (Real.pi + T.beta - T.gamma)
      = T.gamma + ((2 * (i.val : ℤ) - 3 : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_third_add_ne T.gamma _ (m3_gamma_pos T) (m2_gamma_lt T)

/-- `redB i` against `X - Z`. -/
theorem m2_sin_redB_2 (T : OrientedTriangle E o) (i : TrisectorLabel) :
    Real.sin (T.beta + labelAngle i
      - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)) ≠ 0 := by
  have he : T.beta + labelAngle i - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)
      = T.gamma + ((2 * (i.val : ℤ) + 1 : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_third_add_ne T.gamma _ (m3_gamma_pos T) (m2_gamma_lt T)

/-- `redC j` against `Y - X`. -/
theorem m2_sin_redC_0 (T : OrientedTriangle E o) (j : TrisectorLabel) :
    Real.sin (Real.pi - T.gamma - labelAngle j - (T.alpha + 2 * T.beta)) ≠ 0 := by
  have he : Real.pi - T.gamma - labelAngle j - (T.alpha + 2 * T.beta)
      = -T.beta + ((2 - 2 * (j.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_neg_third_add_ne T.beta _ (m3_beta_pos T) (m2_beta_lt T)

/-- `redC j` against `Z - Y`. -/
theorem m2_sin_redC_1 (T : OrientedTriangle E o) (j : TrisectorLabel) :
    Real.sin (Real.pi - T.gamma - labelAngle j - (Real.pi + T.beta - T.gamma)) ≠ 0 := by
  have he : Real.pi - T.gamma - labelAngle j - (Real.pi + T.beta - T.gamma)
      = -T.beta + ((0 - 2 * (j.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_neg_third_add_ne T.beta _ (m3_beta_pos T) (m2_beta_lt T)

/-- `redC j` against `X - Z`. -/
theorem m2_sin_redC_2 (T : OrientedTriangle E o) (j : TrisectorLabel) :
    Real.sin (Real.pi - T.gamma - labelAngle j
      - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)) ≠ 0 := by
  have he : Real.pi - T.gamma - labelAngle j - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)
      = -T.beta + ((4 - 2 * (j.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_neg_third_add_ne T.beta _ (m3_beta_pos T) (m2_beta_lt T)

/-- `greenC i` against `Y - X`. -/
theorem m2_sin_greenC_0 (T : OrientedTriangle E o) (i : TrisectorLabel) :
    Real.sin (Real.pi - 2 * T.gamma + labelAngle i - (T.alpha + 2 * T.beta)) ≠ 0 := by
  have he : Real.pi - 2 * T.gamma + labelAngle i - (T.alpha + 2 * T.beta)
      = T.alpha + ((2 * (i.val : ℤ) + 1 : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_third_add_ne T.alpha _ (m3_alpha_pos T) (m2_alpha_lt T)

/-- `greenC i` against `Z - Y`. -/
theorem m2_sin_greenC_1 (T : OrientedTriangle E o) (i : TrisectorLabel) :
    Real.sin (Real.pi - 2 * T.gamma + labelAngle i - (Real.pi + T.beta - T.gamma)) ≠ 0 := by
  have he : Real.pi - 2 * T.gamma + labelAngle i - (Real.pi + T.beta - T.gamma)
      = T.alpha + ((2 * (i.val : ℤ) - 1 : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_third_add_ne T.alpha _ (m3_alpha_pos T) (m2_alpha_lt T)

/-- `greenC i` against `X - Z`. -/
theorem m2_sin_greenC_2 (T : OrientedTriangle E o) (i : TrisectorLabel) :
    Real.sin (Real.pi - 2 * T.gamma + labelAngle i
      - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)) ≠ 0 := by
  have he : Real.pi - 2 * T.gamma + labelAngle i
        - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)
      = T.alpha + ((2 * (i.val : ℤ) + 3 : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_third_add_ne T.alpha _ (m3_alpha_pos T) (m2_alpha_lt T)

/-- `greenA j` against `Y - X`. -/
theorem m2_sin_greenA_0 (T : OrientedTriangle E o) (j : TrisectorLabel) :
    Real.sin (2 * T.alpha + 3 * T.beta - Real.pi - labelAngle j
      - (T.alpha + 2 * T.beta)) ≠ 0 := by
  have he : 2 * T.alpha + 3 * T.beta - Real.pi - labelAngle j - (T.alpha + 2 * T.beta)
      = -T.gamma + ((-2 - 2 * (j.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_neg_third_add_ne T.gamma _ (m3_gamma_pos T) (m2_gamma_lt T)

/-- `greenA j` against `Z - Y`. -/
theorem m2_sin_greenA_1 (T : OrientedTriangle E o) (j : TrisectorLabel) :
    Real.sin (2 * T.alpha + 3 * T.beta - Real.pi - labelAngle j
      - (Real.pi + T.beta - T.gamma)) ≠ 0 := by
  have he : 2 * T.alpha + 3 * T.beta - Real.pi - labelAngle j - (Real.pi + T.beta - T.gamma)
      = -T.gamma + ((-4 - 2 * (j.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_neg_third_add_ne T.gamma _ (m3_gamma_pos T) (m2_gamma_lt T)

/-- `greenA j` against `X - Z`. -/
theorem m2_sin_greenA_2 (T : OrientedTriangle E o) (j : TrisectorLabel) :
    Real.sin (2 * T.alpha + 3 * T.beta - Real.pi - labelAngle j
      - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)) ≠ 0 := by
  have he : 2 * T.alpha + 3 * T.beta - Real.pi - labelAngle j
        - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)
      = -T.gamma + ((0 - 2 * (j.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_neg_third_add_ne T.gamma _ (m3_gamma_pos T) (m2_gamma_lt T)

/-- `blueA i` against `Y - X`. -/
theorem m2_sin_blueA_0 (T : OrientedTriangle E o) (i : TrisectorLabel) :
    Real.sin (T.alpha + 3 * T.beta - Real.pi + labelAngle i - (T.alpha + 2 * T.beta)) ≠ 0 := by
  have he : T.alpha + 3 * T.beta - Real.pi + labelAngle i - (T.alpha + 2 * T.beta)
      = T.beta + ((-3 + 2 * (i.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_third_add_ne T.beta _ (m3_beta_pos T) (m2_beta_lt T)

/-- `blueA i` against `Z - Y`. -/
theorem m2_sin_blueA_1 (T : OrientedTriangle E o) (i : TrisectorLabel) :
    Real.sin (T.alpha + 3 * T.beta - Real.pi + labelAngle i
      - (Real.pi + T.beta - T.gamma)) ≠ 0 := by
  have he : T.alpha + 3 * T.beta - Real.pi + labelAngle i - (Real.pi + T.beta - T.gamma)
      = T.beta + ((-5 + 2 * (i.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_third_add_ne T.beta _ (m3_beta_pos T) (m2_beta_lt T)

/-- `blueA i` against `X - Z`. -/
theorem m2_sin_blueA_2 (T : OrientedTriangle E o) (i : TrisectorLabel) :
    Real.sin (T.alpha + 3 * T.beta - Real.pi + labelAngle i
      - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)) ≠ 0 := by
  have he : T.alpha + 3 * T.beta - Real.pi + labelAngle i
        - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)
      = T.beta + ((-1 + 2 * (i.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_third_add_ne T.beta _ (m3_beta_pos T) (m2_beta_lt T)

/-- `blueB j` against `Y - X`. -/
theorem m2_sin_blueB_0 (T : OrientedTriangle E o) (j : TrisectorLabel) :
    Real.sin (2 * T.beta - labelAngle j - (T.alpha + 2 * T.beta)) ≠ 0 := by
  have he : 2 * T.beta - labelAngle j - (T.alpha + 2 * T.beta)
      = -T.alpha + ((0 - 2 * (j.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_neg_third_add_ne T.alpha _ (m3_alpha_pos T) (m2_alpha_lt T)

/-- `blueB j` against `Z - Y`. -/
theorem m2_sin_blueB_1 (T : OrientedTriangle E o) (j : TrisectorLabel) :
    Real.sin (2 * T.beta - labelAngle j - (Real.pi + T.beta - T.gamma)) ≠ 0 := by
  have he : 2 * T.beta - labelAngle j - (Real.pi + T.beta - T.gamma)
      = -T.alpha + ((-2 - 2 * (j.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_neg_third_add_ne T.alpha _ (m3_alpha_pos T) (m2_alpha_lt T)

/-- `blueB j` against `X - Z`. -/
theorem m2_sin_blueB_2 (T : OrientedTriangle E o) (j : TrisectorLabel) :
    Real.sin (2 * T.beta - labelAngle j
      - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)) ≠ 0 := by
  have he : 2 * T.beta - labelAngle j - (T.gamma + 2 * T.alpha + 3 * T.beta - Real.pi)
      = -T.alpha + ((2 - 2 * (j.val : ℤ) : ℤ) : ℝ) * (Real.pi / 3) := by
    rw [labelAngle]; push_cast
    have hang : T.alpha + T.beta + T.gamma = Real.pi / 3 := by linarith [T.angle_sum]
    linarith only [hang]
  rw [he]
  exact m2_sin_neg_third_add_ne T.alpha _ (m3_alpha_pos T) (m2_alpha_lt T)

/-! ## 6. No trisector is parallel to a Morley side -/

theorem m2_rho_ne (T : OrientedTriangle E o) :
    (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) ≠ 0 := by
  have h1 := m7_delta_pos T
  have h2 := m7_sin_alpha_pos T
  have h3 := m7_sin_beta_pos T
  have h4 := m7_sin_gamma_pos T
  positivity

theorem m2_not_par_smul {u : E} (hu : u ≠ 0) {r s θ φ : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (h : Real.sin (φ - θ) ≠ 0) :
    ¬ Parallel (r • rotateVector o u θ) (s • rotateVector o u φ) := by
  intro hpar
  rw [m3_par_smul_iff hr hs] at hpar
  exact m3_not_par_rot hu h hpar

theorem m2_redB_not_par (T : OrientedTriangle E o) (i d : TrisectorLabel) :
    ¬ Parallel (m3pSide T d) (T.redB i).direction := by
  have ha : T.aStar ≠ 0 := m3_aStar_ne T
  have hr : (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) ≠ 0 :=
    m2_rho_ne T
  have hL : T.aLength ≠ 0 := ne_of_gt T.aLength_pos
  rcases zmod3_cases d with rfl | rfl | rfl
  · rw [m3p_side_zero, m2_side0_rot, m2_redB_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_redB_0 T i)
  · rw [m3p_side_one, m2_side1_rot, m2_redB_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_redB_1 T i)
  · rw [m3p_side_two, m2_side2_rot, m2_redB_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_redB_2 T i)

theorem m2_redC_not_par (T : OrientedTriangle E o) (j d : TrisectorLabel) :
    ¬ Parallel (m3pSide T d) (T.redC j).direction := by
  have ha : T.aStar ≠ 0 := m3_aStar_ne T
  have hr : (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) ≠ 0 :=
    m2_rho_ne T
  have hL : T.bLength ≠ 0 := ne_of_gt T.bLength_pos
  rcases zmod3_cases d with rfl | rfl | rfl
  · rw [m3p_side_zero, m2_side0_rot, m2_redC_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_redC_0 T j)
  · rw [m3p_side_one, m2_side1_rot, m2_redC_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_redC_1 T j)
  · rw [m3p_side_two, m2_side2_rot, m2_redC_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_redC_2 T j)

theorem m2_greenC_not_par (T : OrientedTriangle E o) (i d : TrisectorLabel) :
    ¬ Parallel (m3pSide T d) (T.greenC i).direction := by
  have ha : T.aStar ≠ 0 := m3_aStar_ne T
  have hr : (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) ≠ 0 :=
    m2_rho_ne T
  have hL : T.bLength ≠ 0 := ne_of_gt T.bLength_pos
  rcases zmod3_cases d with rfl | rfl | rfl
  · rw [m3p_side_zero, m2_side0_rot, m2_greenC_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_greenC_0 T i)
  · rw [m3p_side_one, m2_side1_rot, m2_greenC_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_greenC_1 T i)
  · rw [m3p_side_two, m2_side2_rot, m2_greenC_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_greenC_2 T i)

theorem m2_greenA_not_par (T : OrientedTriangle E o) (j d : TrisectorLabel) :
    ¬ Parallel (m3pSide T d) (T.greenA j).direction := by
  have ha : T.aStar ≠ 0 := m3_aStar_ne T
  have hr : (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) ≠ 0 :=
    m2_rho_ne T
  have hL : T.cLength ≠ 0 := ne_of_gt T.cLength_pos
  rcases zmod3_cases d with rfl | rfl | rfl
  · rw [m3p_side_zero, m2_side0_rot, m2_greenA_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_greenA_0 T j)
  · rw [m3p_side_one, m2_side1_rot, m2_greenA_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_greenA_1 T j)
  · rw [m3p_side_two, m2_side2_rot, m2_greenA_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_greenA_2 T j)

theorem m2_blueA_not_par (T : OrientedTriangle E o) (i d : TrisectorLabel) :
    ¬ Parallel (m3pSide T d) (T.blueA i).direction := by
  have ha : T.aStar ≠ 0 := m3_aStar_ne T
  have hr : (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) ≠ 0 :=
    m2_rho_ne T
  have hL : T.cLength ≠ 0 := ne_of_gt T.cLength_pos
  rcases zmod3_cases d with rfl | rfl | rfl
  · rw [m3p_side_zero, m2_side0_rot, m2_blueA_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_blueA_0 T i)
  · rw [m3p_side_one, m2_side1_rot, m2_blueA_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_blueA_1 T i)
  · rw [m3p_side_two, m2_side2_rot, m2_blueA_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_blueA_2 T i)

theorem m2_blueB_not_par (T : OrientedTriangle E o) (j d : TrisectorLabel) :
    ¬ Parallel (m3pSide T d) (T.blueB j).direction := by
  have ha : T.aStar ≠ 0 := m3_aStar_ne T
  have hr : (4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma) ≠ 0 :=
    m2_rho_ne T
  have hL : T.aLength ≠ 0 := ne_of_gt T.aLength_pos
  rcases zmod3_cases d with rfl | rfl | rfl
  · rw [m3p_side_zero, m2_side0_rot, m2_blueB_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_blueB_0 T j)
  · rw [m3p_side_one, m2_side1_rot, m2_blueB_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_blueB_1 T j)
  · rw [m3p_side_two, m2_side2_rot, m2_blueB_rot]
    exact m2_not_par_smul (o := o) ha hr hL (m2_sin_blueB_2 T j)

/-! ## 7. The non-diagonal family: `m3HPnd` -/

/-- A non-diagonal pair of labels with different sums shares its first or its second
label. -/
theorem m2_pair_row_or_col (p q : TrisectorLabel × TrisectorLabel) (hne : p ≠ q)
    (hsum : p.1 + p.2 ≠ q.1 + q.2) (hnd : ¬ m3Diag p q) : p.1 = q.1 ∨ p.2 = q.2 := by
  revert hne hsum hnd
  revert p q
  decide

theorem m2_par_of_par_of_par {u v w : E} (hv : v ≠ 0) (h1 : Parallel v w) (h2 : Parallel u v) :
    Parallel u w := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  exact ⟨a * b, by rw [ha, hb, smul_smul]⟩

/-- **The non-diagonal exclusion family, unconditionally**: for every oriented triangle
with injective constellation, two distinct same-colour constellation points with different
label sums and different label differences have a join which is not parallel to any
Morley side.  This is `m3HPnd` of `M3G`. -/
theorem m2_m3HPnd (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    m3HPnd T := by
  intro c p q hpq hsum hnd d hpar
  have hrow := m2_pair_row_or_col p q hpq hsum hnd
  have hne_pt : T.constellationPoint ⟨c, p.1, p.2⟩ ≠ T.constellationPoint ⟨c, q.1, q.2⟩ := by
    intro hc
    have hcc := h hc
    exact hpq (by
      rw [Prod.ext_iff]
      exact ⟨congrArg ConstellationIndex.first hcc, congrArg ConstellationIndex.second hcc⟩)
  have hΔ : T.constellationPoint ⟨c, q.1, q.2⟩ - T.constellationPoint ⟨c, p.1, p.2⟩ ≠ 0 :=
    sub_ne_zero.mpr hne_pt.symm
  rcases hrow with hrow | hcol
  · rcases c with _ | _ | _
    · have hm1 : (T.redB p.1).mem (T.constellationPoint ⟨.red, p.1, p.2⟩) :=
        m4_cp_red_mem_redB T p.1 p.2
      have hm2 : (T.redB p.1).mem (T.constellationPoint ⟨.red, q.1, q.2⟩) := by
        rw [← hrow]
        exact m4_cp_red_mem_redB T p.1 q.2
      have hj : Parallel (T.redB p.1).direction
          (T.constellationPoint ⟨.red, q.1, q.2⟩ - T.constellationPoint ⟨.red, p.1, p.2⟩) :=
        Line.parallel_of_mem_sub hm1 hm2
      exact m2_redB_not_par T p.1 d
        (m2_par_of_par_of_par hΔ
          (parallel_comm (T.redB p.1).direction_ne_zero hΔ hj) hpar)
    · have hm1 : (T.greenC p.1).mem (T.constellationPoint ⟨.green, p.1, p.2⟩) :=
        m6_constellation_mem_greenC T p.1 p.2
      have hm2 : (T.greenC p.1).mem (T.constellationPoint ⟨.green, q.1, q.2⟩) := by
        rw [← hrow]
        exact m6_constellation_mem_greenC T p.1 q.2
      have hj : Parallel (T.greenC p.1).direction
          (T.constellationPoint ⟨.green, q.1, q.2⟩ -
            T.constellationPoint ⟨.green, p.1, p.2⟩) :=
        Line.parallel_of_mem_sub hm1 hm2
      exact m2_greenC_not_par T p.1 d
        (m2_par_of_par_of_par hΔ
          (parallel_comm (T.greenC p.1).direction_ne_zero hΔ hj) hpar)
    · have hm1 : (T.blueA p.1).mem (T.constellationPoint ⟨.blue, p.1, p.2⟩) :=
        m6_constellation_mem_blueA T p.1 p.2
      have hm2 : (T.blueA p.1).mem (T.constellationPoint ⟨.blue, q.1, q.2⟩) := by
        rw [← hrow]
        exact m6_constellation_mem_blueA T p.1 q.2
      have hj : Parallel (T.blueA p.1).direction
          (T.constellationPoint ⟨.blue, q.1, q.2⟩ -
            T.constellationPoint ⟨.blue, p.1, p.2⟩) :=
        Line.parallel_of_mem_sub hm1 hm2
      exact m2_blueA_not_par T p.1 d
        (m2_par_of_par_of_par hΔ
          (parallel_comm (T.blueA p.1).direction_ne_zero hΔ hj) hpar)
  · rcases c with _ | _ | _
    · have hm1 : (T.redC p.2).mem (T.constellationPoint ⟨.red, p.1, p.2⟩) :=
        m4_cp_red_mem_redC T p.1 p.2
      have hm2 : (T.redC p.2).mem (T.constellationPoint ⟨.red, q.1, q.2⟩) := by
        rw [← hcol]
        exact m4_cp_red_mem_redC T q.1 p.2
      have hj : Parallel (T.redC p.2).direction
          (T.constellationPoint ⟨.red, q.1, q.2⟩ - T.constellationPoint ⟨.red, p.1, p.2⟩) :=
        Line.parallel_of_mem_sub hm1 hm2
      exact m2_redC_not_par T p.2 d
        (m2_par_of_par_of_par hΔ
          (parallel_comm (T.redC p.2).direction_ne_zero hΔ hj) hpar)
    · have hm1 : (T.greenA p.2).mem (T.constellationPoint ⟨.green, p.1, p.2⟩) :=
        m6_constellation_mem_greenA T p.1 p.2
      have hm2 : (T.greenA p.2).mem (T.constellationPoint ⟨.green, q.1, q.2⟩) := by
        rw [← hcol]
        exact m6_constellation_mem_greenA T q.1 p.2
      have hj : Parallel (T.greenA p.2).direction
          (T.constellationPoint ⟨.green, q.1, q.2⟩ -
            T.constellationPoint ⟨.green, p.1, p.2⟩) :=
        Line.parallel_of_mem_sub hm1 hm2
      exact m2_greenA_not_par T p.2 d
        (m2_par_of_par_of_par hΔ
          (parallel_comm (T.greenA p.2).direction_ne_zero hΔ hj) hpar)
    · have hm1 : (T.blueB p.2).mem (T.constellationPoint ⟨.blue, p.1, p.2⟩) :=
        m6_constellation_mem_blueB T p.1 p.2
      have hm2 : (T.blueB p.2).mem (T.constellationPoint ⟨.blue, q.1, q.2⟩) := by
        rw [← hcol]
        exact m6_constellation_mem_blueB T q.1 p.2
      have hj : Parallel (T.blueB p.2).direction
          (T.constellationPoint ⟨.blue, q.1, q.2⟩ -
            T.constellationPoint ⟨.blue, p.1, p.2⟩) :=
        Line.parallel_of_mem_sub hm1 hm2
      exact m2_blueB_not_par T p.2 d
        (m2_par_of_par_of_par hΔ
          (parallel_comm (T.blueB p.2).direction_ne_zero hΔ hj) hpar)

end OrientedTriangle
end XamboMorley
