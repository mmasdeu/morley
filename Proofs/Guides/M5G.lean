import M5B
import m8_diag11

/-!
# M5G — the diagonal glue for `guideLines_card`

This file is pure assembly.

**1. The sum identity.**  The three Morley side vectors sum to zero,
`(Y-X) + (Z-Y) + (X-Z) = 0`.  Hence for any vector `v`

  `Im (v · conj (Y-X)) + Im (v · conj (Z-Y)) + Im (v · conj (X-Z)) = 0`.

So for the join `v` of two red points, **two strictly same-signed nonparallelity
witnesses already exclude the third Morley side**, with no trigonometry at all
(`not_par_of_two_pos`, `not_par_of_two_neg`).  This is the `m7_im_omega_sum`
step of `.ultramath/smwh60xql/m7` in the direct (`m8`) framework.

**2. The bridge.**  "The join of the two red points is parallel to no Morley
side" implies `M5B`'s `hnd` hypothesis (`hnd_of_not_par`) and hence the upper
bound `T.guideLines.ncard ≤ 9` (`ncard_le_nine_of_not_par`).

**3. Row indexing.**  Each of the nine diagonal pairs is `{(i,j),(i+1,j+1)}`
for exactly one `(i,j)` (`diag_index`), so nine row lemmas assemble directly
(`hnd_of_rows`, `ncard_le_nine_of_rows`).

No `sorry`, no `admit`, no new axiom (`M5G_ax.lean`).
-/

noncomputable section

open scoped Real RealInnerProductSpace ComplexConjugate
open Function Set

namespace XamboMorley
namespace OrientedTriangle
namespace M5G

open XamboMorley.OrientedTriangle.OrientedTriangle
open XamboMorley.OrientedTriangle.M8

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! ## 0. Composing parallelisms -/

theorem par_of_par_par {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {a b c : F}
    (h1 : Parallel a b) (h2 : Parallel b c) : Parallel a c := by
  obtain ⟨r, hr⟩ := h1
  obtain ⟨s, hs⟩ := h2
  exact ⟨s * r, by rw [hs, hr, smul_smul]⟩

/-! ## 1. The three side vectors sum to zero -/

theorem side_sum (T : OrientedTriangle E o) :
    m3pSide T 0 + m3pSide T 1 + m3pSide T 2 = 0 := by
  rw [m3p_side_zero, m3p_side_one, m3p_side_two]
  abel

/-- The imaginary-part sum identity: the three test numbers of a vector against
the three Morley sides add up to `0`. -/
theorem im_sum (T : OrientedTriangle E o) (v : E) :
    (XamboMorley.toComplex o v * star (XamboMorley.toComplex o (m3pSide T 0))).im +
      (XamboMorley.toComplex o v * star (XamboMorley.toComplex o (m3pSide T 1))).im +
      (XamboMorley.toComplex o v * star (XamboMorley.toComplex o (m3pSide T 2))).im = 0 := by
  have hs : XamboMorley.toComplex o (m3pSide T 0) + XamboMorley.toComplex o (m3pSide T 1) +
      XamboMorley.toComplex o (m3pSide T 2) = 0 := by
    rw [← XamboMorley.toComplex_add, ← XamboMorley.toComplex_add, side_sum,
      XamboMorley.toComplex_zero]
  have hs2 : star (XamboMorley.toComplex o (m3pSide T 0)) +
      star (XamboMorley.toComplex o (m3pSide T 1)) +
      star (XamboMorley.toComplex o (m3pSide T 2)) = 0 := by
    rw [← star_add, ← star_add, hs, star_zero]
  have hkey : XamboMorley.toComplex o v *
      (star (XamboMorley.toComplex o (m3pSide T 0)) +
        star (XamboMorley.toComplex o (m3pSide T 1)) +
        star (XamboMorley.toComplex o (m3pSide T 2))) = 0 := by
    rw [hs2, mul_zero]
  have him := congrArg Complex.im hkey
  simp only [Complex.add_im, Complex.zero_im, mul_add] at him ⊢
  linarith [him]

/-! ## 2. Nonvanishing of the test number excludes parallelism -/

theorem not_par_of_im_ne (T : OrientedTriangle E o) {v : E} {k : TrisectorLabel}
    (h : (XamboMorley.toComplex o v * star (XamboMorley.toComplex o (m3pSide T k))).im ≠ 0) :
    ¬ Parallel (m3pSide T k) v :=
  fun hpar => h (par_imp_im T hpar)

/-- Two strictly positive entries force nonparallelity against all three sides. -/
theorem not_par_of_two_pos (T : OrientedTriangle E o) (v : E)
    (h0 : 0 < (XamboMorley.toComplex o v * star (XamboMorley.toComplex o (m3pSide T 0))).im)
    (h2 : 0 < (XamboMorley.toComplex o v * star (XamboMorley.toComplex o (m3pSide T 2))).im) :
    ∀ k : TrisectorLabel, ¬ Parallel (m3pSide T k) v := by
  have hsum := im_sum (o := o) T v
  intro k
  rcases zmod3_cases k with rfl | rfl | rfl
  · exact not_par_of_im_ne T (ne_of_gt h0)
  · refine not_par_of_im_ne T (ne_of_lt ?_)
    linarith
  · exact not_par_of_im_ne T (ne_of_gt h2)

/-- Two strictly negative entries force nonparallelity against all three sides. -/
theorem not_par_of_two_neg (T : OrientedTriangle E o) (v : E)
    (h0 : (XamboMorley.toComplex o v * star (XamboMorley.toComplex o (m3pSide T 0))).im < 0)
    (h2 : (XamboMorley.toComplex o v * star (XamboMorley.toComplex o (m3pSide T 2))).im < 0) :
    ∀ k : TrisectorLabel, ¬ Parallel (m3pSide T k) v := by
  have hsum := im_sum (o := o) T v
  intro k
  rcases zmod3_cases k with rfl | rfl | rfl
  · exact not_par_of_im_ne T (ne_of_lt h0)
  · refine not_par_of_im_ne T (ne_of_gt ?_)
    linarith
  · exact not_par_of_im_ne T (ne_of_lt h2)

/-! ## 3. From side nonparallelity to `M5B`'s `hnd` -/

/-- A guide line carries two diagonal red points only if their join is parallel
to a Morley side. -/
theorem hnd_of_not_par (T : OrientedTriangle E o)
    (h : ∀ (p q : TrisectorLabel × TrisectorLabel), p ≠ q → p.2 - p.1 = q.2 - q.1 →
      ∀ k : TrisectorLabel, ¬ Parallel (m3pSide T k) (m5_redPt T q - m5_redPt T p)) :
    ∀ (p q : TrisectorLabel × TrisectorLabel), p ≠ q → p.2 - p.1 = q.2 - q.1 →
      ∀ ℓ : Line E, ℓ ∈ T.guideLines →
        ¬ (ℓ.mem (m5_redPt T p) ∧ ℓ.mem (m5_redPt T q)) := by
  intro p q hpq hdiag ℓ hℓ hmem
  obtain ⟨hp, hq⟩ := hmem
  have hjoin : Parallel ℓ.direction (m5_redPt T q - m5_redPt T p) := m5_par_of_mem hp hq
  rcases hℓ.1.1 with hside | hside | hside
  · have hs0 : Parallel (m3pSide T 0) ℓ.direction := by
      rw [m3p_side_zero]; exact hside
    exact h p q hpq hdiag 0 (par_of_par_par hs0 hjoin)
  · have hs1 : Parallel (m3pSide T 1) ℓ.direction := by
      rw [m3p_side_one]; exact hside
    exact h p q hpq hdiag 1 (par_of_par_par hs1 hjoin)
  · have hs2 : Parallel (m3pSide T 2) ℓ.direction := by
      rw [m3p_side_two]; exact hside
    exact h p q hpq hdiag 2 (par_of_par_par hs2 hjoin)

/-- **The upper bound from nine join nonparallelities.** -/
theorem ncard_le_nine_of_not_par (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hpar : ∀ (p q : TrisectorLabel × TrisectorLabel), p ≠ q → p.2 - p.1 = q.2 - q.1 →
      ∀ k : TrisectorLabel, ¬ Parallel (m3pSide T k) (m5_redPt T q - m5_redPt T p)) :
    T.guideLines.ncard ≤ 9 :=
  m5_ncard_le_nine_of_diag_join T h (hnd_of_not_par T hpar)

/-! ## 4. Row indexing of the nine diagonal pairs -/

theorem zmod3_add_two_add_one (a : TrisectorLabel) : a + 2 + 1 = a := by revert a; decide

theorem diag_index (p q : TrisectorLabel × TrisectorLabel) (hpq : p ≠ q)
    (hd : p.2 - p.1 = q.2 - q.1) :
    q = (p.1 + 1, p.2 + 1) ∨ q = (p.1 + 2, p.2 + 2) := by
  revert hpq hd
  revert p q
  decide

/-- **Assembly, row form.**  Nine "row" exclusions, one for each `(i,j)`, already
give `M5B`'s `hnd`. -/
theorem hnd_of_rows (T : OrientedTriangle E o)
    (h : ∀ (i j : TrisectorLabel) (ℓ : Line E), ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (m5_redPt T (i, j)) ∧ ℓ.mem (m5_redPt T (i + 1, j + 1)))) :
    ∀ (p q : TrisectorLabel × TrisectorLabel), p ≠ q → p.2 - p.1 = q.2 - q.1 →
      ∀ ℓ : Line E, ℓ ∈ T.guideLines →
        ¬ (ℓ.mem (m5_redPt T p) ∧ ℓ.mem (m5_redPt T q)) := by
  intro p q hpq hd ℓ hℓ hmem
  rcases diag_index p q hpq hd with hq | hq
  · have hp : ℓ.mem (m5_redPt T (p.1, p.2)) := hmem.1
    have hq' : ℓ.mem (m5_redPt T (p.1 + 1, p.2 + 1)) := by rw [← hq]; exact hmem.2
    exact h p.1 p.2 ℓ hℓ ⟨hp, hq'⟩
  · have hq1 : q.1 + 1 = p.1 := by rw [hq]; exact zmod3_add_two_add_one p.1
    have hq2 : q.2 + 1 = p.2 := by rw [hq]; exact zmod3_add_two_add_one p.2
    have hp' : ℓ.mem (m5_redPt T (q.1 + 1, q.2 + 1)) := by rw [hq1, hq2]; exact hmem.1
    exact h q.1 q.2 ℓ hℓ ⟨hmem.2, hp'⟩

/-- **The upper bound in row form.** -/
theorem ncard_le_nine_of_rows (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hrow : ∀ (i j : TrisectorLabel) (ℓ : Line E), ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (m5_redPt T (i, j)) ∧ ℓ.mem (m5_redPt T (i + 1, j + 1)))) :
    T.guideLines.ncard ≤ 9 :=
  m5_ncard_le_nine_of_diag_join T h (hnd_of_rows T hrow)

end M5G
end OrientedTriangle
end XamboMorley
