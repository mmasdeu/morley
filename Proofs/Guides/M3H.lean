/-
  Member m3 (swarm smwh7aexl), direction d9: TRISECTOR_VS_SIDE.

  Discharging actual geometry: no trisector at `B` is parallel to the Morley side `XY`.
  Two same-colour constellation points sharing a trisector have that trisector as their
  join, so this is one complete family of the non-diagonal (`m3HPnd`) exclusions, for every
  triangle with a nondegenerate `ABC`.

  Method: the root gives `Y - X = rho • rotateVector aStar (alpha + 2 beta)` (`Y_sub_X`,
  rho > 0) and the trisector direction is `aLength • rotateVector aStar (beta + labelAngle i)`.
  Two rotations of the same vector are parallel only when `sin` of the angle difference
  vanishes, and `sin (alpha + beta - labelAngle i) != 0` because `alpha + beta` lies strictly
  between `0` and `pi/3` (the root's `m6_sin_sub_nat_pi_three_ne_zero`).
-/
import M3A

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

/-! ### Parallelism is invariant under nonzero rescaling -/

theorem m3_par_smul_iff {u v : E} {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    Parallel (r • u) (s • v) ↔ Parallel u v := by
  constructor
  · rintro ⟨a, ha⟩
    have h1 : s • v = (a * r) • u := by rw [ha, smul_smul]
    have h2 : v = s⁻¹ • (s • v) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    refine ⟨s⁻¹ * (a * r), ?_⟩
    rw [h2, h1, smul_smul]
  · rintro ⟨a, ha⟩
    refine ⟨s * a * r⁻¹, ?_⟩
    rw [ha, smul_smul, smul_smul]
    congr 1
    field_simp

/-! ### Two rotations of one vector are parallel only for a multiple of `pi` -/

theorem m3_not_par_rot {u : E} (hu : u ≠ 0) {s t : ℝ}
    (h : Real.sin (t - s) ≠ 0) : ¬ Parallel (rotateVector o u s) (rotateVector o u t) := by
  intro hpar
  obtain ⟨r, hr⟩ := hpar
  set a := toComplex o u with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hu
  have h' := congrArg (toComplex o) hr
  simp only [toComplex_rotateVector, toComplex_smul] at h'
  have h2 : (Circle.exp t : ℂ) = (r : ℂ) * (Circle.exp s : ℂ) := by
    refine mul_left_cancel₀ ha0 ?_
    rw [h']
    ring
  have h3 : (Circle.exp (t - s) : ℂ) = (r : ℂ) := by
    have hmul : (Circle.exp t : ℂ) * (Circle.exp (-s) : ℂ) =
        (r : ℂ) * ((Circle.exp s : ℂ) * (Circle.exp (-s) : ℂ)) := by
      rw [h2]
      ring
    rw [m6_circle_exp_mul, m6_circle_exp_mul, show s + -s = 0 by ring] at hmul
    simp only [Circle.exp_zero, Circle.coe_one, mul_one] at hmul
    rwa [show t + -s = t - s by ring] at hmul
  have him := congrArg Complex.im h3
  simp only [m6_circle_exp_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero] at him
  exact h (by simpa using him)

/-! ### The Morley side `XY` and the trisectors at `B`, both as rotations of `aStar` -/

theorem m3_side0_rot (T : OrientedTriangle E o) :
    Parallel (rotateVector o T.aStar (T.alpha + 2 * T.beta)) (T.Y - T.X) :=
  ⟨4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma, Y_sub_X T⟩

theorem m3_aStar_ne (T : OrientedTriangle E o) : T.aStar ≠ 0 := by
  intro h0
  have h := m7_norm_aStar T
  rw [h0, norm_zero] at h
  exact absurd h.symm (by norm_num)

theorem m3_CB_smul (T : OrientedTriangle E o) : T.C - T.B = T.aLength • T.aStar :=
  a_eq T

end OrientedTriangle
end XamboMorley
