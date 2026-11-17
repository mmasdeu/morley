import XamboMorleyBase

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set

namespace XamboMorley

universe u

namespace OrientedTriangle

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! ### The `m3c` normal-form pieces that are not in the root

`m3cDrho/Dgam/Dlam/LamNum`, the cleared denominator `m3cD`, the numerators `m3cNA` (for
`green(j,k) - red(i,j)`) and `m3cNBp` (for an equal-sum red join), the non-vanishing
`m3c_D_ne`, and the two cleared identities `m3c_first_mul`, `m3c_red_mul_eq`.
The rest of the `m3c` reduction (`m3c_real_div`, `m3c_hfirst_of_collinear`,
`m3c_tricolor_sides_parallel`, `m3cLam`, `m3c_star_*`, …) is already in the root. -/

noncomputable def m3cDrho (T : OrientedTriangle E o) (i j : TrisectorLabel) : ℂ :=
  1 - m1P T * m1Q T * m1sigma (i + j)

noncomputable def m3cDgam (T : OrientedTriangle E o) (j k : TrisectorLabel) : ℂ :=
  1 - m1Q T * m1R T * m1sigma (j + k)

noncomputable def m3cDlam (T : OrientedTriangle E o) : ℂ := (m1R T) ^ 3 * ((m1P T) ^ 3 - 1)

noncomputable def m3cLamNum (T : OrientedTriangle E o) : ℂ := (m1R T) ^ 3 - 1

noncomputable def m3cD (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) : ℂ :=
  m3cDgam T j k * m3cDlam T * m3cDrho T i j * m3cDrho T i' j'

noncomputable def m3cNA (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) : ℂ :=
  m1Q T * m1sigma j * (1 - m1R T * m1sigma k) * m3cDlam T * m3cDrho T i j
      * m3cDrho T i' j'
    + m3cLamNum T * (1 - m1P T * m1sigma i) * m3cDgam T j k * m3cDrho T i' j'

theorem m3c_D_ne (T : OrientedTriangle E o) (i j k i' j') :
    m3cD T i j k i' j' ≠ 0 := by
  unfold m3cD m3cDgam m3cDlam m3cDrho
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (m1_green_den_ne T (j + k))
    (mul_ne_zero (pow_ne_zero 3 (m3c_R_ne T)) (m3c_P_cube_sub_one_ne T)))
    (m1_red_den_ne T (i + j))) (m1_red_den_ne T (i' + j'))

theorem m3c_red_den2 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 - m1Q T * m1P T * m1sigma s) ≠ 0 := by
  rw [show (1 - m1Q T * m1P T * m1sigma s) = (1 - m1P T * m1Q T * m1sigma s) from by ring]
  exact m1_red_den_ne T s

theorem m3c_green_den2 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 - m1R T * m1Q T * m1sigma s) ≠ 0 := by
  rw [show (1 - m1R T * m1Q T * m1sigma s) = (1 - m1Q T * m1R T * m1sigma s) from by ring]
  exact m1_green_den_ne T s

/-- The `σ`-arguments that `field_simp` produces in the other order. -/
theorem m3c_sig_ji (i j : TrisectorLabel) : m1sigma (j + i) = m1sigma (i + j) := by
  rw [add_comm]

/-- Cleared numerator for an **equal-sum** red join: `NB'` with
`red(i,j) - red(i',j')` (times the common denominator `m3cD`) equal to `NB'·(C-A)`.
This replaces the previous run's `m3c_red_mul`, whose right-hand side carried
`LamNum` against a left-hand side carrying `Dlam = R³(P³-1)`, so it was not provable. -/
noncomputable def m3cNBp (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) : ℂ :=
  m3cLamNum T * m1P T * (m1sigma i' - m1sigma i) * m3cDgam T j k * m3cDrho T i' j'

theorem m3c_red_mul_eq (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel)
    (hs : i + j = i' + j') :
    toComplex o (T.constellationPoint ⟨.red, i, j⟩ - T.constellationPoint ⟨.red, i', j'⟩)
        * m3cD T i j k i' j'
      = m3cNBp T i j k i' j' * toComplex o (T.C - T.A) := by
  conv_lhs => rw [toComplex_sub]
  rw [m1_red_class_diff T i j i' j' hs, m3c_U_eq]
  unfold m3cNBp m3cD m3cDrho m3cDgam m3cDlam m3cLamNum m3cLam
  field_simp [m1_red_den_ne T (i + j), m1_green_den_ne T (j + k),
    m1_red_den_ne T (i' + j'), m3c_red_den2 T (i + j), m3c_green_den2 T (j + k),
    m3c_red_den2 T (i' + j'), m3c_P_cube_sub_one_ne T, m3c_P_ne T, m3c_R_ne T]

/-- `green(j,k) - red(i,j)`, times the common denominator, is `-NA·(C-A)`. -/
theorem m3c_first_mul (T : OrientedTriangle E o) (i j k i' j' : TrisectorLabel) :
    toComplex o (T.constellationPoint ⟨.green, j, k⟩ - T.constellationPoint ⟨.red, i, j⟩)
        * m3cD T i j k i' j'
      = -(m3cNA T i j k i' j') * toComplex o (T.C - T.A) := by
  rw [toComplex_sub, toComplex_sub, m1_green_nf, m1_red_nf, m3c_U_eq]
  unfold m3cD m3cNA m3cDrho m3cDgam m3cDlam m3cLamNum m3cLam
  simp only [toComplex_sub]
  field_simp [m1_red_den_ne T (i + j), m1_green_den_ne T (j + k),
    m1_red_den_ne T (i' + j'), m3c_red_den2 T (i + j), m3c_green_den2 T (j + k),
    m3c_red_den2 T (i' + j'), m3c_P_cube_sub_one_ne T, m3c_P_ne T, m3c_R_ne T]
  simp only [m1sigma_mul, show (i + j : TrisectorLabel) = j + i from by abel,
    show (j + k : TrisectorLabel) = k + j from by abel,
    show (i' + j' : TrisectorLabel) = j' + i' from by abel]
  ring_nf

theorem m3c_sig_kj (j k : TrisectorLabel) : m1sigma (k + j) = m1sigma (j + k) := by
  rw [add_comm]

end OrientedTriangle

end XamboMorley
