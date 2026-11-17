import m8_trig

/-!
# m8 — the diagonal-pair exclusion for the labels `(0,0)`, `(1,1)`

The first of the nine exclusions of `M8.DiagExcl`: the join of `red(0,0)` and `red(1,1)`
is parallel to **no** Morley side, hence no guide line carries both points.

Method (the template for the other eight pairs).  With `P = e^{2iβ}`, `Q = e^{2iγ}` and
the Möbius normal form of `m8_trig.lean`,

* the scalar `1 - P σ_i` is `-2i e^{i(β - ∠i/2)} sin(β - ∠i/2)`;
* hence `ratio(0,0) = e^{-iγ} A` and `ratio(1,1) = e^{i(π/3-γ)} A'` with the **real**
  numbers `A = sin β / sin(β+γ)` and `A' = sin(β-π/3) / sin(β+γ-2π/3)`;
* the join is `(B-C) (ratio(1,1) - ratio(0,0))` and the three Morley side vectors are
  `-ρ · frame · ω^{2-k}`;
* parallel to side `k` forces (after cancelling the common frame and `c = toComplex aStar`,
  `‖c‖ = 1`) `Im ((ratio(1,1) - ratio(0,0)) · conj(e^{i(β-γ)}ω^{2-k})) = 0`, i.e. one of
  three explicit real equations `V_k = 0`, `V_k = A' sin φ'_k - A sin φ_k`;
* `V_2 = A' sin(π/3-β) + A sin β > 0`, while `V_0 < 0` and `V_1 < 0` reduce to
  `sin x < sin(2π/3 - x)` for `x ∈ (0, π/3)` and to monotonicity of
  `x ↦ sin x / sin(2π/3 - x)`.

Nothing here is a `sorry`, an `admit` or a new axiom (`m8_axcheck4.lean`).
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

/-! ## 1. Elementary facts about `star` on unit complex numbers -/

theorem m8_star_ofReal (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := by
  apply Complex.ext <;> simp

theorem star_circle_exp (θ : ℝ) :
    star (Circle.exp θ : ℂ) = (Circle.exp (-θ) : ℂ) := by
  rw [m3c_star_eq_inv (Circle.norm_coe _), Circle.exp_neg, Circle.coe_inv]

theorem omega_mul_sq : (omega : ℂ) * (omega : ℂ) ^ 2 = 1 := by
  calc (omega : ℂ) * (omega : ℂ) ^ 2 = (omega : ℂ) ^ (1 + 2) := by rw [pow_add, pow_one]
    _ = (omega : ℂ) ^ 3 := by norm_num
    _ = 1 := omega_cubed

theorem star_omega : star (omega : ℂ) = (omega : ℂ) ^ 2 := by
  have h : ‖(omega : ℂ)‖ = 1 := Circle.norm_coe _
  rw [m3c_star_eq_inv h]
  exact inv_eq_of_mul_eq_one_right omega_mul_sq

theorem star_omega_sq : star ((omega : ℂ) ^ 2) = (omega : ℂ) := by
  rw [star_pow, star_omega, ← pow_mul]
  rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, omega_cubed, one_mul, pow_one]

/-! ## 2. The three Morley side vectors in the frame -/

theorem side_zero_nf (T : OrientedTriangle E o) :
    XamboMorley.toComplex o (m3pSide T 0) =
      ↑(-(m3pRho T)) * (m3pFrame T * (omega : ℂ) ^ 2) := by
  rw [m3p_side_zero]; exact m3p_Z_YX T

theorem side_one_nf (T : OrientedTriangle E o) :
    XamboMorley.toComplex o (m3pSide T 1) = ↑(-(m3pRho T)) * m3pFrame T := by
  rw [m3p_side_one]
  simpa using m3p_Z_ZY T

theorem side_two_nf (T : OrientedTriangle E o) :
    XamboMorley.toComplex o (m3pSide T 2) =
      ↑(-(m3pRho T)) * (m3pFrame T * (omega : ℂ)) := by
  rw [m3p_side_two]; exact m3p_Z_XZ T

theorem frame_eq (T : OrientedTriangle E o) :
    m3pFrame T = XamboMorley.toComplex o T.aStar * (Circle.exp (T.beta - T.gamma) : ℂ) := rfl

theorem aStar_ne (T : OrientedTriangle E o) : XamboMorley.toComplex o T.aStar ≠ 0 := by
  intro h
  have h1 := m7_norm_aStar T
  rw [← XamboMorley.toComplex_norm (o := o) T.aStar, h, norm_zero] at h1
  norm_num at h1

theorem aStar_normSq (T : OrientedTriangle E o) :
    XamboMorley.toComplex o T.aStar * star (XamboMorley.toComplex o T.aStar) = 1 := by
  have h1 : Complex.normSq (XamboMorley.toComplex o T.aStar) = 1 := by
    rw [Complex.normSq_eq_norm_sq, XamboMorley.toComplex_norm, m7_norm_aStar]
    norm_num
  calc XamboMorley.toComplex o T.aStar * star (XamboMorley.toComplex o T.aStar)
      = ↑(Complex.normSq (XamboMorley.toComplex o T.aStar)) :=
        Complex.mul_conj (XamboMorley.toComplex o T.aStar)
    _ = ↑(1 : ℝ) := by rw [h1]
    _ = 1 := by norm_num


/-! ## 3. The two ratio values for the pair -/

theorem ratio11 (T : OrientedTriangle E o) :
    (1 - m1P T * m1sigma (1 : TrisectorLabel)) /
        (1 - m1P T * m1Q T * m1sigma (2 : TrisectorLabel)) =
      (Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
          - T.gamma) : ℂ) *
        ((Real.sin (T.beta - labelAngle (1 : TrisectorLabel) / 2) /
          Real.sin (T.beta + T.gamma - labelAngle (2 : TrisectorLabel) / 2) : ℝ) : ℂ) := by
  have h := red_mobius (T := T) 1 1
  rwa [show ((1 : TrisectorLabel) + 1) = 2 from by decide] at h

theorem ratio00 (T : OrientedTriangle E o) :
    (1 - m1P T * m1sigma (0 : TrisectorLabel)) /
        (1 - m1P T * m1Q T * m1sigma (0 : TrisectorLabel)) =
      (Circle.exp (-T.gamma) : ℂ) *
        ((Real.sin (T.beta - labelAngle (0 : TrisectorLabel) / 2) /
          Real.sin (T.beta + T.gamma - labelAngle (0 : TrisectorLabel) / 2) : ℝ) : ℂ) := by
  have h := red_mobius (T := T) 0 0
  rw [show ((0 : TrisectorLabel) + 0) = 0 from rfl] at h
  simpa [labelAngle_zero] using h

/-- The real ratios attached to the two points of the pair. -/
noncomputable def rA (T : OrientedTriangle E o) : ℝ :=
  Real.sin (T.beta - labelAngle (0 : TrisectorLabel) / 2) /
    Real.sin (T.beta + T.gamma - labelAngle (0 : TrisectorLabel) / 2)

noncomputable def rA' (T : OrientedTriangle E o) : ℝ :=
  Real.sin (T.beta - labelAngle (1 : TrisectorLabel) / 2) /
    Real.sin (T.beta + T.gamma - labelAngle (2 : TrisectorLabel) / 2)

theorem rA_eq (T : OrientedTriangle E o) : rA T = Real.sin T.beta / Real.sin (T.beta + T.gamma) := by
  unfold rA
  rw [labelAngle_zero]
  norm_num

/-! ## 4. The join against the side `Z - Y` (`k = 1`) -/

theorem join_eq (T : OrientedTriangle E o) :
    XamboMorley.toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
        T.constellationPoint ⟨.red, 0, 0⟩)
      = (-(↑T.aLength) * XamboMorley.toComplex o T.aStar) *
        ((Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
            - T.gamma) : ℂ) * (Complex.ofReal (rA' T)) - (Circle.exp (-T.gamma) : ℂ) * (Complex.ofReal (rA T))) := by
  rw [red_diff_nf, show ((1 : TrisectorLabel) + 1) = 2 from by decide,
    show ((0 : TrisectorLabel) + 0) = 0 from by rfl, ratio11, ratio00, m3p_W_eq, rA, rA']
  ring_nf

theorem ratio_diff_fact (T : OrientedTriangle E o) :
    ((Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
        - T.gamma) : ℂ) * (Complex.ofReal (rA' T)) - (Circle.exp (-T.gamma) : ℂ) *
          (Complex.ofReal (rA T))) * star (Circle.exp (T.beta - T.gamma) : ℂ)
    = (Complex.ofReal (rA' T)) * (Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
        - T.beta) : ℂ) - (Complex.ofReal (rA T)) * (Circle.exp (-T.beta) : ℂ) := by
  have h1 : (Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
      - T.gamma) : ℂ) * star (Circle.exp (T.beta - T.gamma) : ℂ)
      = (Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
          - T.beta) : ℂ) := by
    rw [star_circle_exp, m6_circle_exp_mul]
    congr 1
    congr 1
    ring
  have h2 : (Circle.exp (-T.gamma) : ℂ) * star (Circle.exp (T.beta - T.gamma) : ℂ)
      = (Circle.exp (-T.beta) : ℂ) := by
    rw [star_circle_exp, m6_circle_exp_mul]
    congr 1
    congr 1
    ring
  rw [sub_mul]
  linear_combination (Complex.ofReal (rA' T)) * h1 - (Complex.ofReal (rA T)) * h2


/-! ## 5. The imaginary part against the side `Z - Y` -/

theorem im_side_one (T : OrientedTriangle E o) :
    ((XamboMorley.toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
        T.constellationPoint ⟨.red, 0, 0⟩)) *
      star (XamboMorley.toComplex o (m3pSide T 1))).im
      = T.aLength * m3pRho T *
        (rA' T * Real.sin ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
          - T.beta) + rA T * Real.sin T.beta) := by
  set c := XamboMorley.toComplex o T.aStar with hc
  set E := (Circle.exp (T.beta - T.gamma) : ℂ) with hE
  set X := (Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
      - T.gamma) : ℂ) * Complex.ofReal (rA' T) - (Circle.exp (-T.gamma) : ℂ) *
        Complex.ofReal (rA T) with hX
  have haa : c * star c = 1 := aStar_normSq T
  have hkey : (-(↑(T.aLength)) * c * X) * star (-(↑(m3pRho T)) * (c * E))
      = ↑(T.aLength) * ↑(m3pRho T) * (X * star E) := by
    have hs1 : star (-(↑(m3pRho T)) * (c * E)) = -(↑(m3pRho T)) * (star c * star E) := by
      rw [star_mul, star_mul, star_neg, m8_star_ofReal]
      ring
    rw [hs1]
    linear_combination (↑(T.aLength) * ↑(m3pRho T) * (X * star E)) * haa
  have hjoin : XamboMorley.toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) = -(↑(T.aLength)) * c * X := by
    rw [join_eq, ← hc, ← hX]
  have hside : XamboMorley.toComplex o (m3pSide T 1) = -(↑(m3pRho T)) * (c * E) := by
    rw [side_one_nf, frame_eq, ← hc, ← hE]
    push_cast
    ring
  rw [hjoin, hside, hkey, hX, show (↑(T.aLength) : ℂ) * ↑(m3pRho T) = ↑(T.aLength * m3pRho T) from by
    push_cast; ring]
  rw [ratio_diff_fact]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [Complex.sub_im, m6_im_real_mul_exp, m6_im_real_mul_exp, Real.sin_neg]
  ring


/-! ## 6. Parallelism forces the imaginary part to vanish -/

theorem im_mul_star_self (z : ℂ) : (z * star z).im = 0 := by
  have h : star z = (starRingEnd ℂ) z := rfl
  rw [h, Complex.mul_conj, Complex.ofReal_im]

theorem par_imp_im (T : OrientedTriangle E o) {v : E} {k : TrisectorLabel}
    (hpar : Parallel (m3pSide T k) v) :
    ((XamboMorley.toComplex o v) * star (XamboMorley.toComplex o (m3pSide T k))).im = 0 := by
  obtain ⟨r, hr⟩ := hpar
  rw [hr, XamboMorley.toComplex_smul]
  rw [show (↑r * XamboMorley.toComplex o (m3pSide T k)) *
      star (XamboMorley.toComplex o (m3pSide T k))
      = ↑r * (XamboMorley.toComplex o (m3pSide T k) *
        star (XamboMorley.toComplex o (m3pSide T k))) from by ring]
  rw [Complex.mul_im, im_mul_star_self, mul_zero, Complex.ofReal_im, zero_mul, add_zero]

/-! ## 7. Positivity of the three trigonometric expressions -/

theorem rA'_eq (T : OrientedTriangle E o) :
    rA' T = Real.sin (T.beta - Real.pi / 3) / Real.sin (T.beta + T.gamma - 2 * Real.pi / 3) := by
  unfold rA'
  rw [labelAngle_one, labelAngle_two]
  norm_num
  ring_nf

theorem angle_two_sub_one (T : OrientedTriangle E o) :
    (labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2 = Real.pi / 3 := by
  rw [labelAngle_one, labelAngle_two]
  ring

theorem rA_pos (T : OrientedTriangle E o) : 0 < rA T := by
  rw [rA_eq]
  have hbg := T.m6_beta_add_gamma_bounds_lt
  have hbπ : T.beta < Real.pi := by
    have := m3_gamma_pos T
    linarith [hbg.2, Real.pi_pos]
  have hbgπ : T.beta + T.gamma < Real.pi := by linarith [hbg.2, Real.pi_pos]
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi (m3_beta_pos T) hbπ)
    (Real.sin_pos_of_pos_of_lt_pi hbg.1 hbgπ)

theorem rA'_pos (T : OrientedTriangle E o) : 0 < rA' T := by
  rw [rA'_eq]
  have hbg := T.m6_beta_add_gamma_bounds_lt
  have hβ := m3_beta_pos T
  have hγ := m3_gamma_pos T
  have h1 : Real.sin (T.beta - Real.pi / 3) < 0 := by
    have hp : 0 < Real.sin (Real.pi / 3 - T.beta) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hbg.2, hγ]) (by linarith [Real.pi_pos, hβ])
    rw [show T.beta - Real.pi / 3 = -(Real.pi / 3 - T.beta) from by ring, Real.sin_neg]
    linarith
  have h2 : Real.sin (T.beta + T.gamma - 2 * Real.pi / 3) < 0 := by
    have hp : 0 < Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma)) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hbg.2]) (by linarith [hbg.1, hbg.2])
    rw [show T.beta + T.gamma - 2 * Real.pi / 3
      = -(2 * Real.pi / 3 - (T.beta + T.gamma)) from by ring, Real.sin_neg]
    linarith
  exact div_pos_of_neg_of_neg h1 h2

theorem V_one_pos (T : OrientedTriangle E o) :
    0 < rA' T * Real.sin ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
      - T.beta) + rA T * Real.sin T.beta := by
  have hbg := T.m6_beta_add_gamma_bounds_lt
  have hA : (0 : ℝ) < rA' T := rA'_pos T
  have hB : (0 : ℝ) < rA T := rA_pos T
  have h1 : (0 : ℝ) < Real.sin (Real.pi / 3 - T.beta) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hbg.2, m3_gamma_pos T, m3_beta_pos T])
      (by linarith [Real.pi_pos, m3_beta_pos T])
  have h2 : (0 : ℝ) < Real.sin T.beta :=
    Real.sin_pos_of_pos_of_lt_pi (m3_beta_pos T)
      (by linarith [hbg.2, Real.pi_pos, m3_gamma_pos T])
  have hang : (labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
      = Real.pi / 3 := by
    rw [labelAngle_one, labelAngle_two]; ring
  rw [hang]
  have e1 : (0 : ℝ) < rA' T * Real.sin (Real.pi / 3 - T.beta) := mul_pos hA h1
  have e2 : (0 : ℝ) < rA T * Real.sin T.beta := mul_pos hB h2
  linarith [e1, e2]

/-- **The join of `red(0,0)` and `red(1,1)` is not parallel to the side `Z - Y`.** -/
theorem not_par_side_one (T : OrientedTriangle E o) :
    ¬ Parallel (m3pSide T 1) (T.constellationPoint ⟨.red, 1, 1⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) := by
  intro hpar
  have h0 := par_imp_im T hpar
  rw [im_side_one] at h0
  have hV := V_one_pos T
  have hρ : 0 < m3pRho T := m3p_rho_pos T
  have ha : 0 < T.aLength := aLength_pos T
  nlinarith [h0, hV, mul_pos ha hρ]


/-! ## 8. The same for the side `X - Z` (`k = 2`, `star ω = ω²`) -/

theorem omega_sq_as_exp : (omega : ℂ) ^ 2 = (Circle.exp (4 * Real.pi / 3) : ℂ) :=
  m3p_omega_sq_exp

theorem omega_as_exp : (omega : ℂ) = (Circle.exp (2 * Real.pi / 3) : ℂ) := rfl

theorem ratio_diff_fact_two (T : OrientedTriangle E o) :
    ((Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
        - T.gamma) : ℂ) * (Complex.ofReal (rA' T)) - (Circle.exp (-T.gamma) : ℂ) *
          (Complex.ofReal (rA T))) * (star (Circle.exp (T.beta - T.gamma) : ℂ) * (omega : ℂ) ^ 2)
    = (Complex.ofReal (rA' T)) * (Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
        - T.beta + 4 * Real.pi / 3) : ℂ) - (Complex.ofReal (rA T)) *
        (Circle.exp (4 * Real.pi / 3 - T.beta) : ℂ) := by
  have hω : (omega : ℂ) ^ 2 = (Circle.exp (4 * Real.pi / 3) : ℂ) := omega_sq_as_exp
  have h1 : (Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
      - T.beta) : ℂ) * (Circle.exp (4 * Real.pi / 3) : ℂ)
      = (Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
          - T.beta + 4 * Real.pi / 3) : ℂ) := by
    rw [m6_circle_exp_mul]
  have h2 : (Circle.exp (-T.beta) : ℂ) * (Circle.exp (4 * Real.pi / 3) : ℂ)
      = (Circle.exp (4 * Real.pi / 3 - T.beta) : ℂ) := by
    rw [m6_circle_exp_mul]
    congr 1
    congr 1
    ring
  rw [← mul_assoc, ratio_diff_fact, sub_mul, hω]
  linear_combination (Complex.ofReal (rA' T)) * h1 - (Complex.ofReal (rA T)) * h2

theorem im_side_two (T : OrientedTriangle E o) :
    ((XamboMorley.toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
        T.constellationPoint ⟨.red, 0, 0⟩)) *
      star (XamboMorley.toComplex o (m3pSide T 2))).im
      = T.aLength * m3pRho T *
        (-(rA' T) * Real.sin (Real.pi / 3 + T.beta) + rA T * Real.sin (Real.pi / 3 - T.beta)) := by
  set c := XamboMorley.toComplex o T.aStar with hc
  set E := (Circle.exp (T.beta - T.gamma) : ℂ) with hE
  set X := (Circle.exp ((labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
      - T.gamma) : ℂ) * Complex.ofReal (rA' T) - (Circle.exp (-T.gamma) : ℂ) *
        Complex.ofReal (rA T) with hX
  have haa : c * star c = 1 := aStar_normSq T
  have hkey : (-(↑(T.aLength)) * c * X) * star (-(↑(m3pRho T)) * ((c * E) * (omega : ℂ)))
      = ↑(T.aLength) * ↑(m3pRho T) * (X * (star E * (omega : ℂ) ^ 2)) := by
    have hs1 : star (-(↑(m3pRho T)) * ((c * E) * (omega : ℂ)))
        = -(↑(m3pRho T)) * ((star c * star E) * star (omega : ℂ)) := by
      rw [star_mul, star_mul, star_mul, star_neg, m8_star_ofReal]
      ring
    rw [hs1, star_omega]
    linear_combination (↑(T.aLength) * ↑(m3pRho T) * (X * (star E * (omega : ℂ) ^ 2))) * haa
  have hjoin : XamboMorley.toComplex o (T.constellationPoint ⟨.red, 1, 1⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) = -(↑(T.aLength)) * c * X := by
    rw [join_eq, ← hc, ← hX]
  have hside : XamboMorley.toComplex o (m3pSide T 2) = -(↑(m3pRho T)) * ((c * E) * (omega : ℂ)) := by
    rw [side_two_nf, frame_eq, ← hc, ← hE]
    push_cast
    ring
  rw [hjoin, hside, hkey, hX, show (↑(T.aLength) : ℂ) * ↑(m3pRho T) = ↑(T.aLength * m3pRho T) from by
    push_cast; ring]
  rw [ratio_diff_fact_two]
  have hang : (labelAngle (2 : TrisectorLabel) - labelAngle (1 : TrisectorLabel)) / 2
      = Real.pi / 3 := by
    rw [labelAngle_one, labelAngle_two]; ring
  rw [hang]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [Complex.sub_im, m6_im_real_mul_exp, m6_im_real_mul_exp]
  have hs1 : Real.sin (Real.pi + (2 * Real.pi / 3 - T.beta))
      = -Real.sin (Real.pi / 3 + T.beta) := by
    rw [show Real.pi + (2 * Real.pi / 3 - T.beta)
        = (2 * Real.pi / 3 - T.beta) + Real.pi from by ring, Real.sin_add_pi,
      show 2 * Real.pi / 3 - T.beta = Real.pi - (Real.pi / 3 + T.beta) from by ring,
      Real.sin_pi_sub]
  have hs2 : Real.sin (4 * Real.pi / 3 - T.beta) = -Real.sin (Real.pi / 3 - T.beta) := by
    rw [show 4 * Real.pi / 3 - T.beta = (Real.pi / 3 - T.beta) + Real.pi from by ring,
      Real.sin_add_pi]
  rw [show Real.pi / 3 - T.beta + 4 * Real.pi / 3 = Real.pi + (2 * Real.pi / 3 - T.beta) from by ring,
    hs1, hs2]
  ring


/-! ## 9. The trigonometric inequalities -/

theorem sin_lt_sin_two_third_sub {x : ℝ} (h0 : 0 < x) (h1 : x < Real.pi / 3) :
    Real.sin x < Real.sin (2 * Real.pi / 3 - x) := by
  have h : Real.sin (2 * Real.pi / 3 - x) - Real.sin x = Real.sin (Real.pi / 3 - x) := by
    rw [Real.sin_sub_sin]
    have e1 : (2 * Real.pi / 3 - x - x) / 2 = Real.pi / 3 - x := by ring
    have e2 : (2 * Real.pi / 3 - x + x) / 2 = Real.pi / 3 := by ring
    rw [e1, e2, Real.cos_pi_div_three]
    ring
  have hp : 0 < Real.sin (Real.pi / 3 - x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  linarith

theorem sin_beta_sin_phi_lt (T : OrientedTriangle E o) :
    Real.sin T.beta * Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma))
      < Real.sin (2 * Real.pi / 3 - T.beta) * Real.sin (T.beta + T.gamma) := by
  have hkey : Real.sin T.beta * Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma))
      - Real.sin (2 * Real.pi / 3 - T.beta) * Real.sin (T.beta + T.gamma)
      = -Real.sin (2 * Real.pi / 3) * Real.sin T.gamma := by
    rw [Real.sin_sub, Real.sin_sub, Real.sin_add, Real.cos_add]
    linear_combination (-Real.sin (2 * Real.pi / 3) * Real.sin T.gamma) *
      Real.sin_sq_add_cos_sq T.beta
  have h1 : 0 < Real.sin (2 * Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h2 : 0 < Real.sin T.gamma :=
    Real.sin_pos_of_pos_of_lt_pi (m3_gamma_pos T) (by linarith [m3_beta_pos T,
      T.m6_beta_add_gamma_bounds_lt.2, Real.pi_pos])
  nlinarith [hkey, h1, h2]

theorem V_two_neg (T : OrientedTriangle E o) :
    -(rA' T) * Real.sin (Real.pi / 3 + T.beta) + rA T * Real.sin (Real.pi / 3 - T.beta) < 0 := by
  have hbg := T.m6_beta_add_gamma_bounds_lt
  have hβ := m3_beta_pos T
  have hγ := m3_gamma_pos T
  have hs1 : 0 < Real.sin (Real.pi / 3 - T.beta) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hbg.2, hγ, hβ]) (by linarith [Real.pi_pos, hβ])
  have hsφ : 0 < Real.sin (T.beta + T.gamma) :=
    Real.sin_pos_of_pos_of_lt_pi hbg.1 (by linarith [hbg.2, Real.pi_pos])
  have hs2' : 0 < Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma)) := by
    rw [show 2 * Real.pi / 3 - (T.beta + T.gamma)
      = Real.pi - (Real.pi / 3 + (T.beta + T.gamma)) from by ring, Real.sin_pi_sub]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hbg.1, Real.pi_pos])
      (by linarith [hbg.2, Real.pi_pos])
  have hkey := sin_beta_sin_phi_lt T
  have hβπ : Real.sin (T.beta - Real.pi / 3) = -Real.sin (Real.pi / 3 - T.beta) := by
    rw [show T.beta - Real.pi / 3 = -(Real.pi / 3 - T.beta) from by ring, Real.sin_neg]
  have hsum : Real.sin (Real.pi / 3 + T.beta) = Real.sin (2 * Real.pi / 3 - T.beta) := by
    rw [show Real.pi / 3 + T.beta = Real.pi - (2 * Real.pi / 3 - T.beta) from by ring,
      Real.sin_pi_sub]
  have hden : Real.sin (T.beta + T.gamma - 2 * Real.pi / 3)
      = -Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma)) := by
    rw [show T.beta + T.gamma - 2 * Real.pi / 3
      = -(2 * Real.pi / 3 - (T.beta + T.gamma)) from by ring, Real.sin_neg]
  rw [rA'_eq, rA_eq, hβπ, hden]
  have hbr : Real.sin T.beta / Real.sin (T.beta + T.gamma)
      < Real.sin (2 * Real.pi / 3 - T.beta) / Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma)) := by
    have h1 : Real.sin T.beta / Real.sin (T.beta + T.gamma)
        - Real.sin (2 * Real.pi / 3 - T.beta)
          / Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma)) < 0 := by
      rw [div_sub_div _ _ (ne_of_gt hsφ) (ne_of_gt hs2')]
      apply div_neg_of_neg_of_pos
      · linarith [hkey]
      · exact mul_pos hsφ hs2'
    linarith
  rw [hsum]
  have step : -((-Real.sin (Real.pi / 3 - T.beta)) / (-Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma))))
        * Real.sin (2 * Real.pi / 3 - T.beta)
        + Real.sin T.beta / Real.sin (T.beta + T.gamma) * Real.sin (Real.pi / 3 - T.beta)
      = Real.sin (Real.pi / 3 - T.beta) *
        (Real.sin T.beta / Real.sin (T.beta + T.gamma)
          - Real.sin (2 * Real.pi / 3 - T.beta)
            / Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma))) := by
    field_simp
    ring_nf
  rw [step]
  have hbr' : Real.sin T.beta / Real.sin (T.beta + T.gamma)
      - Real.sin (2 * Real.pi / 3 - T.beta) / Real.sin (2 * Real.pi / 3 - (T.beta + T.gamma)) < 0 := by
    linarith [hbr]
  exact mul_neg_of_pos_of_neg hs1 hbr'

/-- **The join of `red(0,0)` and `red(1,1)` is not parallel to the side `X - Z`.** -/
theorem not_par_side_two (T : OrientedTriangle E o) :
    ¬ Parallel (m3pSide T 2) (T.constellationPoint ⟨.red, 1, 1⟩ -
      T.constellationPoint ⟨.red, 0, 0⟩) := by
  intro hpar
  have h0 := par_imp_im T hpar
  rw [im_side_two] at h0
  have hV := V_two_neg T
  have hρ : 0 < m3pRho T := m3p_rho_pos T
  have ha : 0 < T.aLength := aLength_pos T
  nlinarith [h0, hV, mul_pos ha hρ]

end M8





end OrientedTriangle
end XamboMorley
