import m8_core

/-!
# m8 — Möbius normal form of the red joins

The root's normal form of a red constellation point is

  `toComplex (red(i,j)) = C + (B - C) * (1 - P σ_i) / (1 - P Q σ_{i+j})`

with `P = e^{2iβ}`, `Q = e^{2iγ}`, `σ_l = e^{-i∠l}` (`m1_red_nf`).  The Möbius step
`1 - e^{iθ} = -2i e^{iθ/2} sin (θ/2)` (root `m6_one_sub_exp`) makes the ratio a **real**
sine ratio times a unit complex number:

  `(1 - P σ_i)/(1 - P Q σ_{i+j})
     = e^{i((∠(i+j) - ∠i)/2 - γ)} · (sin (β - ∠i/2) / sin (β + γ - ∠(i+j)/2))`.

This is the analytic engine of the exclusion programme: combined with the root's Morley
side dictionary (`m3p_Z_YX` …) it turns "the red join is parallel to a Morley side" into a
single real trigonometric equation.

No `sorry`, no `admit`, no new axiom (`m8_axcheck4.lean`).
-/

noncomputable section

open scoped Real RealInnerProductSpace ComplexConjugate
open Function Set

namespace XamboMorley
namespace OrientedTriangle
namespace M8

open XamboMorley.OrientedTriangle.OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! ## 1. Elementary exponential bookkeeping -/

theorem m1P_eq_exp (T : OrientedTriangle E o) :
    m1P T = (Circle.exp (2 * T.beta) : ℂ) := rfl

theorem m1Q_eq_exp (T : OrientedTriangle E o) :
    m1Q T = (Circle.exp (2 * T.gamma) : ℂ) := rfl

/-- `e^{a} · σ_l = e^{a - ∠ l}`. -/
theorem exp_mul_sigma (a : ℝ) (l : TrisectorLabel) :
    (Circle.exp a : ℂ) * m1sigma l = (Circle.exp (a - labelAngle l) : ℂ) := by
  rw [m1sigma, m6_circle_exp_mul]
  congr 1

theorem one_sub_P_sigma (T : OrientedTriangle E o) (i : TrisectorLabel) :
    (1 : ℂ) - m1P T * m1sigma i =
      -2 * Complex.I * ((Real.sin (T.beta - labelAngle i / 2) : ℝ) : ℂ) *
        (Circle.exp (T.beta - labelAngle i / 2) : ℂ) := by
  have h := m6_one_sub_exp (2 * T.beta - labelAngle i)
  rw [show (2 * T.beta - labelAngle i) / 2 = T.beta - labelAngle i / 2 from by ring] at h
  have hkey : m1P T * m1sigma i = (Circle.exp (2 * T.beta - labelAngle i) : ℂ) := by
    rw [m1P_eq_exp, exp_mul_sigma]
  rw [hkey]
  exact h

theorem one_sub_PQ_sigma (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 : ℂ) - m1P T * m1Q T * m1sigma s =
      -2 * Complex.I * ((Real.sin (T.beta + T.gamma - labelAngle s / 2) : ℝ) : ℂ) *
        (Circle.exp (T.beta + T.gamma - labelAngle s / 2) : ℂ) := by
  have h := m6_one_sub_exp (2 * (T.beta + T.gamma) - labelAngle s)
  rw [show (2 * (T.beta + T.gamma) - labelAngle s) / 2
    = T.beta + T.gamma - labelAngle s / 2 from by ring] at h
  have hkey : m1P T * m1Q T * m1sigma s
      = (Circle.exp (2 * (T.beta + T.gamma) - labelAngle s) : ℂ) := by
    have h2 : (Circle.exp (2 * T.beta) : ℂ) * (Circle.exp (2 * T.gamma) : ℂ) * m1sigma s
        = (Circle.exp (2 * (T.beta + T.gamma) - labelAngle s) : ℂ) := by
      rw [m6_circle_exp_mul, exp_mul_sigma,
        show 2 * T.beta + 2 * T.gamma = 2 * (T.beta + T.gamma) from by ring]
    rw [m1P_eq_exp, m1Q_eq_exp]
    exact h2
  rw [hkey]
  exact h

/-! ## 2. The Möbius normal form of the red ratio -/

/-- **The Möbius normal form of the red ratio**, product form (no division). -/
theorem red_mobius_prod (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    1 - m1P T * m1sigma i =
      ((Circle.exp ((labelAngle (i + j) - labelAngle i) / 2 - T.gamma) : ℂ) *
        ((Real.sin (T.beta - labelAngle i / 2) /
          Real.sin (T.beta + T.gamma - labelAngle (i + j) / 2) : ℝ) : ℂ)) *
        (1 - m1P T * m1Q T * m1sigma (i + j)) := by
  have hBne : Real.sin (T.beta + T.gamma - labelAngle (i + j) / 2) ≠ 0 :=
    m3p_sin_bg_ne T (i + j)
  have hexp : (Circle.exp (T.beta - labelAngle i / 2) : ℂ) =
      (Circle.exp ((labelAngle (i + j) - labelAngle i) / 2 - T.gamma) : ℂ) *
        (Circle.exp (T.beta + T.gamma - labelAngle (i + j) / 2) : ℂ) := by
    rw [← Circle.coe_mul, ← Circle.exp_add]
    congr 1
    congr 1
    ring
  have hsin : ((Real.sin (T.beta - labelAngle i / 2) : ℝ) : ℂ)
      = ((Real.sin (T.beta + T.gamma - labelAngle (i + j) / 2) : ℝ) : ℂ) *
        ((Real.sin (T.beta - labelAngle i / 2) /
          Real.sin (T.beta + T.gamma - labelAngle (i + j) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, mul_div_cancel₀ _ hBne]
  rw [one_sub_P_sigma, one_sub_PQ_sigma, hexp, hsin]
  ring

/-- **The Möbius normal form of the red ratio.** -/
theorem red_mobius (T : OrientedTriangle E o) (i j : TrisectorLabel) :
    (1 - m1P T * m1sigma i) / (1 - m1P T * m1Q T * m1sigma (i + j)) =
      (Circle.exp ((labelAngle (i + j) - labelAngle i) / 2 - T.gamma) : ℂ) *
        ((Real.sin (T.beta - labelAngle i / 2) /
          Real.sin (T.beta + T.gamma - labelAngle (i + j) / 2) : ℝ) : ℂ) := by
  rw [div_eq_iff (m1_red_den_ne T (i + j))]
  exact red_mobius_prod T i j

/-! ## 3. The difference of two red points -/

theorem red_diff_nf (T : OrientedTriangle E o) (i j i' j' : TrisectorLabel) :
    XamboMorley.toComplex o (T.constellationPoint ⟨.red, i', j'⟩ -
        T.constellationPoint ⟨.red, i, j⟩)
      = XamboMorley.toComplex o (T.B - T.C) *
        ((1 - m1P T * m1sigma i') / (1 - m1P T * m1Q T * m1sigma (i' + j')) -
          (1 - m1P T * m1sigma i) / (1 - m1P T * m1Q T * m1sigma (i + j))) := by
  rw [XamboMorley.toComplex_sub, m1_red_nf T i' j', m1_red_nf T i j]
  ring

end M8
end OrientedTriangle
end XamboMorley
