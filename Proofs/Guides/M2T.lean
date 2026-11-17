import M2Base

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

/-! ### The power table for `ω`

The certificates below are Laurent identities in the free variables `P = e^{2iβ}`,
`Q = e^{2iγ}` and the primitive cube root `ω = e^{2iπ/3}`, after `R = e^{2iα}` has been
eliminated through `P Q R = ω`. The only algebraic input is `ω ^ 3 = 1`, tabulated for the
exponents that occur (bounded by 48). -/


theorem m2_om0 : (omega : ℂ) ^ 0 = 1 := by rw [pow_zero]
theorem m2_om1 : (omega : ℂ) ^ 1 = (omega : ℂ) := by rw [pow_one]
theorem m2_om2 : (omega : ℂ) ^ 2 = (omega : ℂ) ^ 2 := rfl
theorem m2_om3 : (omega : ℂ) ^ 3 = 1 := by
  rw [show (3 : ℕ) = 3 * 1 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om4 : (omega : ℂ) ^ 4 = (omega : ℂ) := by
  rw [show (4 : ℕ) = 3 * 1 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om5 : (omega : ℂ) ^ 5 = (omega : ℂ) ^ 2 := by
  rw [show (5 : ℕ) = 3 * 1 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om6 : (omega : ℂ) ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om7 : (omega : ℂ) ^ 7 = (omega : ℂ) := by
  rw [show (7 : ℕ) = 3 * 2 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om8 : (omega : ℂ) ^ 8 = (omega : ℂ) ^ 2 := by
  rw [show (8 : ℕ) = 3 * 2 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om9 : (omega : ℂ) ^ 9 = 1 := by
  rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om10 : (omega : ℂ) ^ 10 = (omega : ℂ) := by
  rw [show (10 : ℕ) = 3 * 3 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om11 : (omega : ℂ) ^ 11 = (omega : ℂ) ^ 2 := by
  rw [show (11 : ℕ) = 3 * 3 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om12 : (omega : ℂ) ^ 12 = 1 := by
  rw [show (12 : ℕ) = 3 * 4 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om13 : (omega : ℂ) ^ 13 = (omega : ℂ) := by
  rw [show (13 : ℕ) = 3 * 4 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om14 : (omega : ℂ) ^ 14 = (omega : ℂ) ^ 2 := by
  rw [show (14 : ℕ) = 3 * 4 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om15 : (omega : ℂ) ^ 15 = 1 := by
  rw [show (15 : ℕ) = 3 * 5 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om16 : (omega : ℂ) ^ 16 = (omega : ℂ) := by
  rw [show (16 : ℕ) = 3 * 5 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om17 : (omega : ℂ) ^ 17 = (omega : ℂ) ^ 2 := by
  rw [show (17 : ℕ) = 3 * 5 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om18 : (omega : ℂ) ^ 18 = 1 := by
  rw [show (18 : ℕ) = 3 * 6 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om19 : (omega : ℂ) ^ 19 = (omega : ℂ) := by
  rw [show (19 : ℕ) = 3 * 6 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om20 : (omega : ℂ) ^ 20 = (omega : ℂ) ^ 2 := by
  rw [show (20 : ℕ) = 3 * 6 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om21 : (omega : ℂ) ^ 21 = 1 := by
  rw [show (21 : ℕ) = 3 * 7 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om22 : (omega : ℂ) ^ 22 = (omega : ℂ) := by
  rw [show (22 : ℕ) = 3 * 7 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om23 : (omega : ℂ) ^ 23 = (omega : ℂ) ^ 2 := by
  rw [show (23 : ℕ) = 3 * 7 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om24 : (omega : ℂ) ^ 24 = 1 := by
  rw [show (24 : ℕ) = 3 * 8 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om25 : (omega : ℂ) ^ 25 = (omega : ℂ) := by
  rw [show (25 : ℕ) = 3 * 8 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om26 : (omega : ℂ) ^ 26 = (omega : ℂ) ^ 2 := by
  rw [show (26 : ℕ) = 3 * 8 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om27 : (omega : ℂ) ^ 27 = 1 := by
  rw [show (27 : ℕ) = 3 * 9 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om28 : (omega : ℂ) ^ 28 = (omega : ℂ) := by
  rw [show (28 : ℕ) = 3 * 9 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om29 : (omega : ℂ) ^ 29 = (omega : ℂ) ^ 2 := by
  rw [show (29 : ℕ) = 3 * 9 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om30 : (omega : ℂ) ^ 30 = 1 := by
  rw [show (30 : ℕ) = 3 * 10 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om31 : (omega : ℂ) ^ 31 = (omega : ℂ) := by
  rw [show (31 : ℕ) = 3 * 10 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om32 : (omega : ℂ) ^ 32 = (omega : ℂ) ^ 2 := by
  rw [show (32 : ℕ) = 3 * 10 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om33 : (omega : ℂ) ^ 33 = 1 := by
  rw [show (33 : ℕ) = 3 * 11 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om34 : (omega : ℂ) ^ 34 = (omega : ℂ) := by
  rw [show (34 : ℕ) = 3 * 11 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om35 : (omega : ℂ) ^ 35 = (omega : ℂ) ^ 2 := by
  rw [show (35 : ℕ) = 3 * 11 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om36 : (omega : ℂ) ^ 36 = 1 := by
  rw [show (36 : ℕ) = 3 * 12 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om37 : (omega : ℂ) ^ 37 = (omega : ℂ) := by
  rw [show (37 : ℕ) = 3 * 12 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om38 : (omega : ℂ) ^ 38 = (omega : ℂ) ^ 2 := by
  rw [show (38 : ℕ) = 3 * 12 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om39 : (omega : ℂ) ^ 39 = 1 := by
  rw [show (39 : ℕ) = 3 * 13 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om40 : (omega : ℂ) ^ 40 = (omega : ℂ) := by
  rw [show (40 : ℕ) = 3 * 13 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om41 : (omega : ℂ) ^ 41 = (omega : ℂ) ^ 2 := by
  rw [show (41 : ℕ) = 3 * 13 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om42 : (omega : ℂ) ^ 42 = 1 := by
  rw [show (42 : ℕ) = 3 * 14 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om43 : (omega : ℂ) ^ 43 = (omega : ℂ) := by
  rw [show (43 : ℕ) = 3 * 14 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om44 : (omega : ℂ) ^ 44 = (omega : ℂ) ^ 2 := by
  rw [show (44 : ℕ) = 3 * 14 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om45 : (omega : ℂ) ^ 45 = 1 := by
  rw [show (45 : ℕ) = 3 * 15 by norm_num, pow_mul, omega_cubed, one_pow]
theorem m2_om46 : (omega : ℂ) ^ 46 = (omega : ℂ) := by
  rw [show (46 : ℕ) = 3 * 15 + 1 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul, pow_one]
theorem m2_om47 : (omega : ℂ) ^ 47 = (omega : ℂ) ^ 2 := by
  rw [show (47 : ℕ) = 3 * 15 + 2 by norm_num, pow_add, pow_mul, omega_cubed,
    one_pow, one_mul]
theorem m2_om48 : (omega : ℂ) ^ 48 = 1 := by
  rw [show (48 : ℕ) = 3 * 16 by norm_num, pow_mul, omega_cubed, one_pow]

/-- Cross-conjugate certificate for the label `(0,0,0)` with red partner
`(2,1)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_000_21 (T : OrientedTriangle E o) :
    star (m3cNBp T 0 0 0 2 1) * (-(m3cNA T 0 0 0 2 1))
      = m3cNBp T 0 0 0 2 1 * star (-(m3cNA T 0 0 0 2 1)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(0,0,2)` with red partner
`(1,2)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_002_12 (T : OrientedTriangle E o) :
    star (m3cNBp T 0 0 2 1 2) * (-(m3cNA T 0 0 2 1 2))
      = m3cNBp T 0 0 2 1 2 * star (-(m3cNA T 0 0 2 1 2)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(0,1,1)` with red partner
`(1,0)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_011_10 (T : OrientedTriangle E o) :
    star (m3cNBp T 0 1 1 1 0) * (-(m3cNA T 0 1 1 1 0))
      = m3cNBp T 0 1 1 1 0 * star (-(m3cNA T 0 1 1 1 0)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(0,1,2)` with red partner
`(2,2)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_012_22 (T : OrientedTriangle E o) :
    star (m3cNBp T 0 1 2 2 2) * (-(m3cNA T 0 1 2 2 2))
      = m3cNBp T 0 1 2 2 2 * star (-(m3cNA T 0 1 2 2 2)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(0,2,0)` with red partner
`(1,1)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_020_11 (T : OrientedTriangle E o) :
    star (m3cNBp T 0 2 0 1 1) * (-(m3cNA T 0 2 0 1 1))
      = m3cNBp T 0 2 0 1 1 * star (-(m3cNA T 0 2 0 1 1)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(0,2,1)` with red partner
`(2,0)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_021_20 (T : OrientedTriangle E o) :
    star (m3cNBp T 0 2 1 2 0) * (-(m3cNA T 0 2 1 2 0))
      = m3cNBp T 0 2 1 2 0 * star (-(m3cNA T 0 2 1 2 0)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(1,0,1)` with red partner
`(2,2)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_101_22 (T : OrientedTriangle E o) :
    star (m3cNBp T 1 0 1 2 2) * (-(m3cNA T 1 0 1 2 2))
      = m3cNBp T 1 0 1 2 2 * star (-(m3cNA T 1 0 1 2 2)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(1,0,2)` with red partner
`(0,1)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_102_01 (T : OrientedTriangle E o) :
    star (m3cNBp T 1 0 2 0 1) * (-(m3cNA T 1 0 2 0 1))
      = m3cNBp T 1 0 2 0 1 * star (-(m3cNA T 1 0 2 0 1)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(1,1,0)` with red partner
`(2,0)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_110_20 (T : OrientedTriangle E o) :
    star (m3cNBp T 1 1 0 2 0) * (-(m3cNA T 1 1 0 2 0))
      = m3cNBp T 1 1 0 2 0 * star (-(m3cNA T 1 1 0 2 0)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(1,1,1)` with red partner
`(0,2)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_111_02 (T : OrientedTriangle E o) :
    star (m3cNBp T 1 1 1 0 2) * (-(m3cNA T 1 1 1 0 2))
      = m3cNBp T 1 1 1 0 2 * star (-(m3cNA T 1 1 1 0 2)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(1,2,0)` with red partner
`(0,0)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_120_00 (T : OrientedTriangle E o) :
    star (m3cNBp T 1 2 0 0 0) * (-(m3cNA T 1 2 0 0 0))
      = m3cNBp T 1 2 0 0 0 * star (-(m3cNA T 1 2 0 0 0)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(1,2,2)` with red partner
`(2,1)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_122_21 (T : OrientedTriangle E o) :
    star (m3cNBp T 1 2 2 2 1) * (-(m3cNA T 1 2 2 2 1))
      = m3cNBp T 1 2 2 2 1 * star (-(m3cNA T 1 2 2 2 1)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(2,0,0)` with red partner
`(0,2)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_200_02 (T : OrientedTriangle E o) :
    star (m3cNBp T 2 0 0 0 2) * (-(m3cNA T 2 0 0 0 2))
      = m3cNBp T 2 0 0 0 2 * star (-(m3cNA T 2 0 0 0 2)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(2,0,1)` with red partner
`(1,1)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_201_11 (T : OrientedTriangle E o) :
    star (m3cNBp T 2 0 1 1 1) * (-(m3cNA T 2 0 1 1 1))
      = m3cNBp T 2 0 1 1 1 * star (-(m3cNA T 2 0 1 1 1)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(2,1,0)` with red partner
`(1,2)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_210_12 (T : OrientedTriangle E o) :
    star (m3cNBp T 2 1 0 1 2) * (-(m3cNA T 2 1 0 1 2))
      = m3cNBp T 2 1 0 1 2 * star (-(m3cNA T 2 1 0 1 2)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(2,1,2)` with red partner
`(0,0)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_212_00 (T : OrientedTriangle E o) :
    star (m3cNBp T 2 1 2 0 0) * (-(m3cNA T 2 1 2 0 0))
      = m3cNBp T 2 1 2 0 0 * star (-(m3cNA T 2 1 2 0 0)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(2,2,1)` with red partner
`(0,1)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_221_01 (T : OrientedTriangle E o) :
    star (m3cNBp T 2 2 1 0 1) * (-(m3cNA T 2 2 1 0 1))
      = m3cNBp T 2 2 1 0 1 * star (-(m3cNA T 2 2 1 0 1)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring

/-- Cross-conjugate certificate for the label `(2,2,2)` with red partner
`(1,0)`: this is the realness of the ratio of the two joins. -/
theorem m2_cross_222_10 (T : OrientedTriangle E o) :
    star (m3cNBp T 2 2 2 1 0) * (-(m3cNA T 2 2 2 1 0))
      = m3cNBp T 2 2 2 1 0 * star (-(m3cNA T 2 2 2 1 0)) := by
  unfold m3cNA m3cNBp m3cDrho m3cDgam m3cDlam m3cLamNum
  rw [m2_R_eq T]
  simp only [    m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_zero, m1sigma_one, m1sigma_two,
    star_add, star_sub, star_mul, star_pow, star_one, star_neg, inv_one,
    m2_star_div, m2_star_inv, m2_star_ofNat, m2_star_omega,
    m3c_star_P T, m3c_star_Q T, m3c_star_sigma, ← pow_mul]
  field_simp [m1P_ne_zero T, m1Q_ne_zero T, omega_ne_zero',
    mul_ne_zero (m1P_ne_zero T) (m1Q_ne_zero T)]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  try ring_nf
  try simp only [m2_sum00, m2_sum01, m2_sum02, m2_sum10, m2_sum11, m2_sum12,
    m2_sum20, m2_sum21, m2_sum22, m1sigma_mul, m1sigma_zero, m1sigma_one,
    m1sigma_two, inv_one, m2_sigma_mul_inv, m2_sigma_inv_mul, m3c_sig_ji, m3c_sig_kj]
  simp only [m2_om3, m2_om4, m2_om5, m2_om6, m2_om7, m2_om8, m2_om9, m2_om10, m2_om11, m2_om12, m2_om13, m2_om14, m2_om15, m2_om16, m2_om17, m2_om18, m2_om19, m2_om20, m2_om21, m2_om22, m2_om23, m2_om24, m2_om25, m2_om26, m2_om27, m2_om28, m2_om29, m2_om30, m2_om31, m2_om32, m2_om33, m2_om34, m2_om35, m2_om36, m2_om37, m2_om38, m2_om39, m2_om40, m2_om41, m2_om42, m2_om43, m2_om44, m2_om45, m2_om46, m2_om47, m2_om48]
  ring


end OrientedTriangle

end XamboMorley
