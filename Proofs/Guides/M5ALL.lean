/-
  Member m5 (swarm smwh1zs5u), direction 5 (EXHAUSTIVE_GUIDE_SET_CLASSIFICATION).

  Verified helper lemmas towards the nine equal-sum joins behind `guideLines`:

  * `m5_key_general`   : `1 - e^{2i(θ - kπ/3)}` relative to `1 - e^{2iθ}` (real factor and
                         the rotation `e^{-ikπ/3}`).
  * `m5_class_den_rot` : the sum-class denominator of class `s` is the class-`0` one
                         rotated by `-s π/3`, rescaled by a real number.
  * `m5_sigma_diff_six`: `σ i' - σ i` is a sixth root of unity times `σ 2 - σ 0`.
  * `m5_red_join_six`  : the join of any equal-sum red pair is a sixth-root multiple of
                         the reference join of its class.
  * `m5_class_ref_join_rot` : the class-`s` reference join is the class-`0` one rotated
                         by `s π/3`, rescaled by a real number.

  No `sorry`, no new axioms, no `admit`; imports the current root `XamboMorley`.
-/
import XamboMorleyBase

noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set

namespace XamboMorley
namespace OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}


/-! ### The exponential factor of a sum class -/

/-- `P Q σ s = exp (2 i (β + γ - s π/3))`. -/
theorem m5_PQ_sigma_eq (T : OrientedTriangle E o) (s : TrisectorLabel) :
    T.m1P * T.m1Q * m1sigma s =
      (Circle.exp (2 * (T.beta + T.gamma - (s.val : ℝ) * Real.pi / 3)) : ℂ) := by
  have hsig : m1sigma s = (Circle.exp (-((s.val : ℝ) * (2 * Real.pi / 3))) : ℂ) := by
    rw [m1sigma, labelAngle]
  rw [m1P, m1Q, hsig, m1_exp_mul, m1_exp_mul]
  rw [show 2 * T.beta + 2 * T.gamma + -(↑(ZMod.val s) * (2 * Real.pi / 3))
      = 2 * (T.beta + T.gamma - ↑(ZMod.val s) * Real.pi / 3) from by ring]

theorem m5_PQ_eq (T : OrientedTriangle E o) :
    T.m1P * T.m1Q = (Circle.exp (2 * (T.beta + T.gamma)) : ℂ) := by
  rw [m1P, m1Q, m1_exp_mul]
  rw [show 2 * T.beta + 2 * T.gamma = 2 * (T.beta + T.gamma) from by ring]

/-- The general rotation identity for `1 - e^{2iθ}`: shifting `θ` by a multiple of `π/3`
multiplies `1 - e^{2iθ}` by a real factor and a rotation by the opposite angle. -/
theorem m5_key_general (θ : ℝ) (m : ℝ) (hθ : Real.sin θ ≠ 0) :
    (1 : ℂ) - (Circle.exp (2 * (θ - m * Real.pi / 3)) : ℂ) =
      ((Real.sin (θ - m * Real.pi / 3) / Real.sin θ : ℝ) : ℂ)
        * (Circle.exp (-(m * Real.pi / 3)) : ℂ) * (1 - (Circle.exp (2 * θ) : ℂ)) := by
  have hexp : (Circle.exp (θ - m * Real.pi / 3) : ℂ)
      = (Circle.exp θ : ℂ) * (Circle.exp (-(m * Real.pi / 3)) : ℂ) := by
    rw [m1_exp_mul]
    congr 2
  have hsinC : ((Real.sin (θ - m * Real.pi / 3) : ℝ) : ℂ)
      = ((Real.sin (θ - m * Real.pi / 3) / Real.sin θ : ℝ) : ℂ)
        * ((Real.sin θ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  have hθC : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact hθ
  rw [m1_one_sub_exp_two (θ - m * Real.pi / 3), m1_one_sub_exp_two θ, hexp, hsinC]
  field_simp

/-! ### The class denominator rotation -/

/-- The red class denominator of sum class `s` is the class-`0` denominator rotated by
`-s π/3`, with the real factor `sin (β+γ - sπ/3) / sin (β+γ)`. -/
theorem m5_class_den_rot (T : OrientedTriangle E o) (s : TrisectorLabel) :
    (1 - T.m1P * T.m1Q * m1sigma s) =
      ((Real.sin (T.beta + T.gamma - (s.val : ℝ) * Real.pi / 3) /
          Real.sin (T.beta + T.gamma) : ℝ) : ℂ)
        * (Circle.exp (-((s.val : ℝ) * Real.pi / 3)) : ℂ)
        * (1 - T.m1P * T.m1Q) := by
  rw [m5_PQ_sigma_eq, m5_PQ_eq]
  exact m5_key_general (T.beta + T.gamma) (s.val : ℝ) T.m6_sin_beta_add_gamma_ne_zero



/-- The six sixth roots of unity, written with `omega = exp (2πi/3)`. -/
def m5Six (z : ℂ) : Prop :=
  z = 1 ∨ z = -1 ∨ z = (omega : ℂ) ∨ z = -(omega : ℂ) ∨
    z = (omega : ℂ) ^ 2 ∨ z = -((omega : ℂ) ^ 2)

theorem m5Six_one : m5Six 1 := Or.inl rfl
theorem m5Six_neg_one : m5Six (-1) := Or.inr (Or.inl rfl)
theorem m5Six_omega : m5Six (omega : ℂ) := Or.inr (Or.inr (Or.inl rfl))
theorem m5Six_neg_omega : m5Six (-(omega : ℂ)) := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem m5Six_omega_sq : m5Six ((omega : ℂ) ^ 2) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
theorem m5Six_neg_omega_sq : m5Six (-((omega : ℂ) ^ 2)) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem m5Six_neg {z : ℂ} (h : m5Six z) : m5Six (-z) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m5Six_neg_one
  · simpa using m5Six_one
  · exact m5Six_neg_omega
  · simpa using m5Six_omega
  · exact m5Six_neg_omega_sq
  · simpa using m5Six_omega_sq

/-- `sigma 2 - sigma 0 != 0`. -/
theorem m5_sigma_two_sub_zero_ne : m1sigma (2 : TrisectorLabel) - m1sigma (0 : TrisectorLabel) ≠ 0 := by
  intro h
  rw [m1sigma_two, m1sigma_zero] at h
  exact w9_omega_ne_one (by linear_combination h)

/-- The label difference `σ i' - σ i` is a sixth root of unity times `σ 2 - σ 0`. -/
theorem m5_sigma_diff_six (i i' : TrisectorLabel) (h : i ≠ i') :
    ∃ z : ℂ, m5Six z ∧
      m1sigma i' - m1sigma i = z * (m1sigma (2 : TrisectorLabel) - m1sigma (0 : TrisectorLabel)) := by
  rcases m4_label_cases i with rfl | rfl | rfl <;>
    rcases m4_label_cases i' with rfl | rfl | rfl
  · exact absurd rfl h
  · refine ⟨-((omega : ℂ) ^ 2), m5Six_neg_omega_sq, ?_⟩
    simp only [m1sigma_zero, m1sigma_one, m1sigma_two]
    linear_combination (omega : ℂ) ^ 0 * omega_cubed
  · refine ⟨1, m5Six_one, ?_⟩
    simp only [m1sigma_zero, m1sigma_one, m1sigma_two]
    ring
  · refine ⟨(omega : ℂ) ^ 2, m5Six_omega_sq, ?_⟩
    simp only [m1sigma_zero, m1sigma_one, m1sigma_two]
    linear_combination -(1 : ℂ) * omega_cubed
  · exact absurd rfl h
  · refine ⟨-(omega : ℂ), m5Six_neg_omega, ?_⟩
    simp only [m1sigma_zero, m1sigma_one, m1sigma_two]
    ring
  · refine ⟨-1, m5Six_neg_one, ?_⟩
    simp only [m1sigma_zero, m1sigma_one, m1sigma_two]
    ring
  · refine ⟨(omega : ℂ), m5Six_omega, ?_⟩
    simp only [m1sigma_zero, m1sigma_one, m1sigma_two]
    ring
  · exact absurd rfl h



/-- The join of ANY equal-sum pair of red points is a sixth root of unity times the
reference join `red(0,s) - red(2,s-2)` of the same sum class. -/
theorem m5_red_join_six (T : OrientedTriangle E o) (i j i' j' : TrisectorLabel)
    (hsum : i + j = i' + j') (hne : (i, j) ≠ (i', j')) :
    ∃ z : ℂ, m5Six z ∧
      toComplex o (T.m5_redPt (i, j) - T.m5_redPt (i', j')) =
        z * toComplex o (T.m5_redPt (0, i + j) - T.m5_redPt (2, i + j - 2)) := by
  have hii : i ≠ i' := by
    rintro rfl
    exact hne (Prod.ext rfl (add_left_cancel hsum))
  obtain ⟨z, hz, hzsig⟩ := m5_sigma_diff_six i i' hii
  have h1 : toComplex o (T.m5_redPt (i, j)) - toComplex o (T.m5_redPt (i', j')) =
      toComplex o (T.B - T.C) * T.m1P * (m1sigma i' - m1sigma i) /
        (1 - T.m1P * T.m1Q * m1sigma (i + j)) := by
    simpa only [m5_redPt] using m1_red_class_diff T i j i' j' hsum
  have h2 : toComplex o (T.m5_redPt (0, i + j)) - toComplex o (T.m5_redPt (2, i + j - 2)) =
      toComplex o (T.B - T.C) * T.m1P * (m1sigma 2 - m1sigma 0) /
        (1 - T.m1P * T.m1Q * m1sigma (i + j)) := by
    have h0 : (0 : TrisectorLabel) + (i + j) = i + j := by ring
    have h := m1_red_class_diff T 0 (i + j) 2 (i + j - 2) (by ring)
    rw [h0] at h
    simpa only [m5_redPt] using h
  have hd : (1 - T.m1P * T.m1Q * m1sigma (i + j)) ≠ 0 := m1_red_den_ne T (i + j)
  refine ⟨z, hz, ?_⟩
  rw [toComplex_sub, toComplex_sub, h1, h2, hzsig]
  field_simp

/-- The reference join of sum class `s` is the class-`0` reference join rotated by `s π/3`
and rescaled by the real number `sin (β+γ) / sin (β+γ - s π/3)`. -/
theorem m5_class_ref_join_rot (T : OrientedTriangle E o) (s : TrisectorLabel) :
    toComplex o (T.m5_redPt (0, s) - T.m5_redPt (2, s - 2)) =
      ((Real.sin (T.beta + T.gamma) /
          Real.sin (T.beta + T.gamma - (s.val : ℝ) * Real.pi / 3) : ℝ) : ℂ)
        * (Circle.exp ((s.val : ℝ) * Real.pi / 3) : ℂ)
        * toComplex o (T.m5_redPt (0, 0) - T.m5_redPt (2, 1)) := by
  have hden := m5_class_den_rot T s
  have hden0 : (1 - T.m1P * T.m1Q * m1sigma (0 : TrisectorLabel)) = 1 - T.m1P * T.m1Q := by
    rw [m1sigma_zero, mul_one]
  have h1 : toComplex o (T.m5_redPt (0, s)) - toComplex o (T.m5_redPt (2, s - 2)) =
      toComplex o (T.B - T.C) * T.m1P * (m1sigma 2 - m1sigma 0) /
        (1 - T.m1P * T.m1Q * m1sigma (0 + s)) := by
    simpa only [m5_redPt] using m1_red_class_diff T 0 s 2 (s - 2) (by ring)
  have h2 : toComplex o (T.m5_redPt (0, 0)) - toComplex o (T.m5_redPt (2, 1)) =
      toComplex o (T.B - T.C) * T.m1P * (m1sigma 2 - m1sigma 0) /
        (1 - T.m1P * T.m1Q * m1sigma (0 + 0)) := by
    simpa only [m5_redPt] using m1_red_class_diff T 0 0 2 1 (by decide)
  have hsin0 : Real.sin (T.beta + T.gamma) ≠ 0 := T.m6_sin_beta_add_gamma_ne_zero
  have hsin : Real.sin (T.beta + T.gamma - (s.val : ℝ) * Real.pi / 3) ≠ 0 := by
    obtain hs | hs | hs := m4_label_cases s
    · rw [hs]; simpa using hsin0
    · rw [hs]; exact T.m1_sin_shift_ne 1
    · rw [hs]; exact T.m1_sin_shift_ne 2
  have hSC : ((Real.sin (T.beta + T.gamma) /
      Real.sin (T.beta + T.gamma - (s.val : ℝ) * Real.pi / 3) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact div_ne_zero hsin0 hsin
  have hEC : (Circle.exp ((s.val : ℝ) * Real.pi / 3) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hDC : (1 - T.m1P * T.m1Q) ≠ 0 := by
    have h := m1_red_den_ne T 0
    rw [m1sigma_zero, mul_one] at h
    exact h
  have hden' : (1 - T.m1P * T.m1Q * m1sigma s) =
      ((Real.sin (T.beta + T.gamma - (s.val : ℝ) * Real.pi / 3) /
          Real.sin (T.beta + T.gamma) : ℝ) : ℂ)
        * (Circle.exp ((s.val : ℝ) * Real.pi / 3) : ℂ)⁻¹
        * (1 - T.m1P * T.m1Q) := by
    rw [hden]
    have hinv : (Circle.exp (-((s.val : ℝ) * Real.pi / 3)) : ℂ)
        = (Circle.exp ((s.val : ℝ) * Real.pi / 3) : ℂ)⁻¹ := by
      rw [← Circle.coe_inv, ← Circle.exp_neg]
    rw [hinv]
  rw [toComplex_sub, toComplex_sub, h1, h2]
  rw [show (0 : TrisectorLabel) + s = s from by ring]
  rw [show (0 : TrisectorLabel) + 0 = 0 from by ring, hden0]
  rw [hden']
  field_simp
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  congr 1
  field_simp

/-! ### Reductions: `guideLines_card` plus the constructive lower bounds

The three guide-line targets of the root are `guideLines_card`, `point_on_two_guideLines`
and `guideLines_direction_card`.  The upper bounds `<= 9`, `<= 2 per point` and
`<= 3 per direction` are the hard (exclusion) half; the lower bounds are constructive.
The two lemmas below show that the *constructive* lower bounds suffice once
`guideLines_card` is known, so no exclusion estimate on points or directions is needed. -/

/-- **Three per direction from the total count.**  If there are exactly nine guide lines and
each of the three Morley side directions carries at least three guide lines, then each
carries exactly three.  (No upper estimate per direction is needed.) -/
theorem m5_direction_card_of_le (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hcard : T.guideLines.ncard ≤ 9)
    (h3 : ∀ v : E, v = T.Y - T.X ∨ v = T.Z - T.Y ∨ v = T.X - T.Z →
      3 ≤ {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard) :
    ∀ v : E, v = T.Y - T.X ∨ v = T.Z - T.Y ∨ v = T.X - T.Z →
      {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard = 3 := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  set A1 := {ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction} with hA1def
  set A2 := {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction} with hA2def
  set A3 := {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction} with hA3def
  have hf1 : A1.Finite := hfin.subset (fun ℓ hℓ => hℓ.1)
  have hf2 : A2.Finite := hfin.subset (fun ℓ hℓ => hℓ.1)
  have hf3 : A3.Finite := hfin.subset (fun ℓ hℓ => hℓ.1)
  obtain ⟨hn1, hn2, hn3⟩ := m4_not_parallel_morley T
  have hcover : T.guideLines = (A1 ∪ A2) ∪ A3 := by
    ext ℓ
    simp only [hA1def, hA2def, hA3def, guideLines, IsGuideLine, parallelToMorleySide,
      Set.mem_ofPred_eq, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hd12 : Disjoint A1 A2 := by
    rw [Set.disjoint_left]
    rintro ℓ ⟨-, hp1⟩ ⟨-, hp2⟩
    exact hn1 (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hp1 hp2)
  have hd23 : Disjoint A2 A3 := by
    rw [Set.disjoint_left]
    rintro ℓ ⟨-, hp1⟩ ⟨-, hp2⟩
    exact hn2 (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hp1 hp2)
  have hd13 : Disjoint A1 A3 := by
    rw [Set.disjoint_left]
    rintro ℓ ⟨-, hp1⟩ ⟨-, hp2⟩
    exact hn3 (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hp2 hp1)
  have hd123 : Disjoint (A1 ∪ A2) A3 := by
    rw [Set.disjoint_left]
    rintro ℓ (hℓ | hℓ) hℓ'
    · exact Set.disjoint_left.mp hd13 hℓ hℓ'
    · exact Set.disjoint_left.mp hd23 hℓ hℓ'
  have hcovercard : T.guideLines.ncard = A1.ncard + A2.ncard + A3.ncard := by
    rw [hcover, m4_ncard_union_of_disjoint (hf1.union hf2) hf3 hd123,
      m4_ncard_union_of_disjoint hf1 hf2 hd12]
  have hsum : A1.ncard + A2.ncard + A3.ncard ≤ 9 := by
    rw [← hcovercard]; exact hcard
  have h1 : 3 ≤ A1.ncard := by rw [hA1def]; exact h3 _ (Or.inl rfl)
  have h2 : 3 ≤ A2.ncard := by rw [hA2def]; exact h3 _ (Or.inr (Or.inl rfl))
  have h3' : 3 ≤ A3.ncard := by rw [hA3def]; exact h3 _ (Or.inr (Or.inr rfl))
  have e1 : A1.ncard = 3 := by omega
  have e2 : A2.ncard = 3 := by omega
  have e3 : A3.ncard = 3 := by omega
  intro v hv
  rcases hv with rfl | rfl | rfl
  · exact e1
  · exact e2
  · exact e3

/-- **Two guide lines through every point from the total count.**  If there are exactly nine
guide lines and every constellation point lies on at least two of them, then every point lies
on exactly two.  (No upper estimate per point is needed.) -/
theorem m5_two_per_point_of_le (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hcard : T.guideLines.ncard ≤ 9)
    (h2 : ∀ q : ConstellationIndex,
      2 ≤ {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard) :
    ∀ q : ConstellationIndex,
      {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2 := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have hcard27 : Fintype.card ConstellationIndex = 27 := by decide
  have hpt : ∀ q : ConstellationIndex,
      2 ≤ (hfin.toFinset.filter (fun ℓ => ℓ.mem (T.constellationPoint q))).card := by
    intro q
    rw [← m4_ncard_sep (fun ℓ => ℓ.mem (T.constellationPoint q)) hfin]
    exact h2 q
  have hline : ∀ ℓ ∈ hfin.toFinset, (m4_ptsOn T ℓ).card = 6 := by
    intro ℓ hℓ
    exact m4_ptsOn_card_of_mem T (hfin.mem_toFinset.mp hℓ)
  have hLle : Finset.sum hfin.toFinset (fun ℓ => (m4_ptsOn T ℓ).card) ≤ 9 * 6 := by
    rw [Finset.sum_congr rfl hline, Finset.sum_const, smul_eq_mul,
      ← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.mul_le_mul_right 6 hcard
  have hsumle : Finset.sum Finset.univ (fun q : ConstellationIndex =>
      (m4_linesOn T hfin q).card) ≤ 27 * 2 := by
    rw [← m4_double_count T hfin]
    exact hLle
  have hsum : Finset.sum Finset.univ (fun q : ConstellationIndex =>
      (hfin.toFinset.filter (fun ℓ => ℓ.mem (T.constellationPoint q))).card) ≤ 27 * 2 := by
    simpa only [m4_linesOn] using hsumle
  intro q
  set g : ConstellationIndex → ℕ := fun q =>
    (hfin.toFinset.filter (fun ℓ => ℓ.mem (T.constellationPoint q))).card with hg
  have hsumg : Finset.sum Finset.univ g ≤ 27 * 2 := hsum
  have hsplit : Finset.sum Finset.univ g = g q + Finset.sum (Finset.univ.erase q) g := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)]
  have hrest2 : 52 ≤ Finset.sum (Finset.univ.erase q) g := by
    have h1 : Finset.sum (Finset.univ.erase q) (fun _ => 2) ≤
        Finset.sum (Finset.univ.erase q) g :=
      Finset.sum_le_sum (fun x _ => hpt x)
    have h2 : Finset.sum (Finset.univ.erase q) (fun _ => 2 : ConstellationIndex → ℕ) = 52 := by
      rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ q),
        Finset.card_univ, hcard27]
    omega
  have hq2 : g q = 2 := by
    have h1 : 2 ≤ g q := by rw [hg]; exact hpt q
    have heq : g q + Finset.sum (Finset.univ.erase q) g ≤ 27 * 2 := by
      rw [← hsplit]; exact hsumg
    omega
  have hconv : {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = g q := by
    rw [m4_ncard_sep (fun ℓ => ℓ.mem (T.constellationPoint q)) hfin, hg]
  rw [hconv, hq2]

/-- **`hclass` from a pair-level statement.**  The hypothesis `hclass` of the root's
`m5_ncard_le_nine` (same-colour points on a guide line have equal label sums) follows from
the purely pair-level non-parallelism statement: no same-colour join of two points with
*unequal* label sums is parallel to a Morley side.  No guide-line or six-point condition is
needed in the hypothesis. -/
theorem m5_hclass_of_pairs (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hpair : ∀ p q : TrisectorLabel × TrisectorLabel, p ≠ q → p.1 + p.2 ≠ q.1 + q.2 →
      ¬ Parallel (T.m5_redPt p - T.m5_redPt q) (T.Y - T.X) ∧
      ¬ Parallel (T.m5_redPt p - T.m5_redPt q) (T.Z - T.Y) ∧
      ¬ Parallel (T.m5_redPt p - T.m5_redPt q) (T.X - T.Z)) :
    ∀ (ℓ : Line E), ℓ ∈ T.guideLines → ∀ p q : TrisectorLabel × TrisectorLabel,
      ℓ.mem (T.m5_redPt p) → ℓ.mem (T.m5_redPt q) → p.1 + p.2 = q.1 + q.2 := by
  intro ℓ hℓ p q hp hq
  by_contra hne
  have hpq : p ≠ q := by
    rintro rfl
    exact hne rfl
  have hne_pt : T.m5_redPt p ≠ T.m5_redPt q := by
    intro hc
    have hidx := h hc
    exact hpq (Prod.ext (by simpa using congrArg ConstellationIndex.first hidx)
      (by simpa using congrArg ConstellationIndex.second hidx))
  obtain ⟨h1, h2, h3⟩ := hpair p q hpq hne
  obtain ⟨t₁, ht₁⟩ := hp
  obtain ⟨t₂, ht₂⟩ := hq
  have hsub : T.m5_redPt p - T.m5_redPt q = (t₁ - t₂) • ℓ.direction := by
    rw [ht₁, ht₂]
    simp only [add_sub_add_left_eq_sub]
    rw [sub_smul]
  have htne : t₁ - t₂ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsub
    exact hne_pt (sub_eq_zero.mp hsub)
  have hpar : Parallel (T.m5_redPt p - T.m5_redPt q) ℓ.direction := by
    refine ⟨(t₁ - t₂)⁻¹, ?_⟩
    rw [hsub, smul_smul, inv_mul_cancel₀ htne, one_smul]
  rcases hℓ.1 with hh | hh | hh
  · exact h1 (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hpar hh)
  · exact h2 (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hpar hh)
  · exact h3 (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hpar hh)

/-- **Guide-line count from the pair-level statement.**  `guideLines.ncard ≤ 9` (the root's
`m5_ncard_le_nine`, whose only remaining hypothesis is `hclass`) follows from the pair-level
non-parallelism statement plus injectivity. -/
theorem m5_ncard_le_nine_of_pairs (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hpair : ∀ p q : TrisectorLabel × TrisectorLabel, p ≠ q → p.1 + p.2 ≠ q.1 + q.2 →
      ¬ Parallel (T.m5_redPt p - T.m5_redPt q) (T.Y - T.X) ∧
      ¬ Parallel (T.m5_redPt p - T.m5_redPt q) (T.Z - T.Y) ∧
      ¬ Parallel (T.m5_redPt p - T.m5_redPt q) (T.X - T.Z)) :
    T.guideLines.ncard ≤ 9 :=
  m5_ncard_le_nine T h (m5_hclass_of_pairs T h hpair)

end OrientedTriangle
end XamboMorley
