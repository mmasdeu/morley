import M5GBC

/-!
# m6 — the blocking (double-counting) upper bound `|guideLines| ≤ 9`

**Main point.**  The upper bound on the number of guide lines does **not** need any
diagonal-pair exclusion, any Mobius/trigonometric computation, or any bare-line
non-parallelism.  It is a *pure incidence-counting* consequence of the compiled
facts alone:

* (i) the nine lines `m4L s d` (`s d : ZMod 3`) are ordinary lines, and the
  compiled certificates `m4Six_red_elim`, `m5_gbc_green_p/q`, `m5_gbc_blue_p/q`
  show that every constellation index `q ∈ m4Six s d` satisfies
  `(m4L s d).mem (cp q)`  (`m6Six_inc` below);
* (ii) each of the 27 constellation indices lies in exactly **two** of the nine
  six-sets `m4Six s d` (`m6Idx_card`, a `decide` fact about labels);
* (iii) two distinct points determine a line (root `m4_mem_iff_of_two_mem`).

Let `ℓ` be a guide line, `P` its six constellation indices.  If `ℓ` were none of the
nine `m4L s d` (up to canonical representative), then no one of the nine lines could
carry two of the points of `P`, so the nine `2`-element index sets `m6Idx q`
(`q ∈ P`) would be pairwise disjoint, and their union would have `6 * 2 = 12 > 9`
elements — impossible inside a 9-element index set.

Hence `guideLines ⊆ {canonical representative of m4L s d}` and
`T.guideLines.ncard ≤ 9`, unconditionally (`m6_guideLines_ncard_le_nine`).
The same argument bounds the number of guide lines parallel to a fixed vector by 3
(`m6_direction_le_three`).

No `sorry`, no `admit`, no new axiom; the only inputs are the root module, `M4Guide`
(via `M5Base`) and `M2P` (via `M5GBC`).
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable section

open Function Set
open XamboMorley
open XamboMorley.OrientedTriangle
open XamboMorley.OrientedTriangle.OrientedTriangle
open XamboMorley.M4

namespace XamboMorley.M6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! ## 1. Every index of `m4Six s d` is carried by the line `m4L s d` -/

/-- **The six expected indices of `m4L s d` are indeed incident.**  Red from the two
defining endpoints, green and blue from the compiled `M2P` certificates
(`m5_gbc_green_p/q`, `m5_gbc_blue_p/q`). -/
theorem m6Six_inc (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) {q : ConstellationIndex} (hq : q ∈ m4Six s d) :
    (m4L T h s d).mem (T.constellationPoint q) := by
  obtain ⟨c, f, g⟩ := q
  cases c with
  | red =>
      rcases m4Six_red_elim s d f g hq with h' | h'
      · rw [h']; exact m4L_mem_p T h s d
      · rw [h']; exact m4L_mem_q T h s d
  | green =>
      rcases m4Six_green_elim s d f g hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact m5_gbc_green_p T h s d
      · exact m5_gbc_green_q T h s d
  | blue =>
      rcases m4Six_blue_elim s d f g hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact m5_gbc_blue_p T h s d
      · exact m5_gbc_blue_q T h s d

/-! ## 2. The index set of a constellation point has two elements -/

/-- The nine-line indices whose six-set contains `q`. -/
def m6Idx (q : ConstellationIndex) : Finset (TrisectorLabel × TrisectorLabel) :=
  Finset.univ.filter (fun p => q ∈ m4Six p.1 p.2)

theorem m6Idx_def (q : ConstellationIndex) :
    m6Idx q = Finset.univ.filter (fun p => q ∈ m4Six p.1 p.2) := rfl

/-- **Each constellation point lies in exactly two of the nine six-sets.**  Pure label
arithmetic (`ZMod 3`), discharged by evaluation. -/
theorem m6Idx_card : ∀ q : ConstellationIndex, (m6Idx q).card = 2 := by
  intro q
  obtain ⟨c, f, g⟩ := q
  cases c <;> revert f g <;> decide

/-! ## 3. The canonical representative of each of the nine lines -/

/-- The `Line.isCanonical` representative of `m4L s d`. -/
def m6Canon (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (p : TrisectorLabel × TrisectorLabel) : Line E :=
  m4Canon o (m4L T h p.1 p.2).base (m4L T h p.1 p.2).direction
    (m4L T h p.1 p.2).direction_ne_zero

theorem m6Canon_isCanonical (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (p : TrisectorLabel × TrisectorLabel) :
    Line.isCanonical o (m6Canon (o := o) T h p) :=
  m4Canon_isCanonical (P := (m4L T h p.1 p.2).base) (v := (m4L T h p.1 p.2).direction)
    o (m4L T h p.1 p.2).direction_ne_zero

theorem m6Canon_mem_iff (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (p : TrisectorLabel × TrisectorLabel) (X : E) :
    (m6Canon (o := o) T h p).mem X ↔ (m4L T h p.1 p.2).mem X :=
  m4Canon_mem_iff (P := (m4L T h p.1 p.2).base) (v := (m4L T h p.1 p.2).direction)
    o (m4L T h p.1 p.2).direction_ne_zero X

theorem m6Canon_direction (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (p : TrisectorLabel × TrisectorLabel) :
    (m6Canon (o := o) T h p).direction = m4Dir o (m4L T h p.1 p.2).direction := rfl

theorem m6Canon_direction_par (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (p : TrisectorLabel × TrisectorLabel) :
    Parallel (m3pSide T p.2) (m6Canon (o := o) T h p).direction := by
  rw [m6Canon_direction]
  exact (m4L_dir_par T h p.1 p.2).trans
    (m4Dir_par (v := (m4L T h p.1 p.2).direction) o (m4L T h p.1 p.2).direction_ne_zero)

/-! ## 4. Two of the nine lines through the same point force a coincidence -/

/-- **If a guide line is not one of the nine canonical lines, its six points have
pairwise disjoint index sets.**  Otherwise one of the nine lines would share two
distinct points with it, hence coincide with it. -/
theorem m6_disjoint (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {ℓ : Line E} (hcan : Line.isCanonical o ℓ)
    (hnot : ∀ p : TrisectorLabel × TrisectorLabel, ℓ ≠ m6Canon (o := o) T h p)
    {q q' : ConstellationIndex} (hne : q ≠ q')
    (hm : ℓ.mem (T.constellationPoint q)) (hm' : ℓ.mem (T.constellationPoint q')) :
    Disjoint (m6Idx q) (m6Idx q') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [m6Idx_def, Finset.mem_filter] at hp hp'
  have h1 : (m4L T h p.1 p.2).mem (T.constellationPoint q) := m6Six_inc T h p.1 p.2 hp.2
  have h2 : (m4L T h p.1 p.2).mem (T.constellationPoint q') := m6Six_inc T h p.1 p.2 hp'.2
  have hpt : T.constellationPoint q ≠ T.constellationPoint q' := fun hh => hne (h hh)
  have hiff := m4_mem_iff_of_two_mem hpt h1 h2 hm hm'
  refine hnot p (isCanonical_eq_of_mem_iff hcan (m6Canon_isCanonical T h p) (fun X => ?_))
  rw [m6Canon_mem_iff]
  exact (hiff X).symm

/-! ## 5. The main theorem -/

/-- **Every guide line is the canonical representative of one of the nine equal-sum
joins.**  Incidence counting with `6 * 2 = 12 > 9`. -/
theorem m6_guide_mem_nine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {ℓ : Line E} (hℓ : ℓ ∈ T.guideLines) :
    ∃ p : TrisectorLabel × TrisectorLabel, ℓ = m6Canon (o := o) T h p := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  have hnot : ∀ p : TrisectorLabel × TrisectorLabel, ℓ ≠ m6Canon (o := o) T h p :=
    fun p he => hcon p he
  simp only [guideLines, Set.mem_ofPred_eq] at hℓ
  obtain ⟨hisg, hcan⟩ := hℓ
  set PF : Finset ConstellationIndex :=
    Finset.univ.filter (fun q => ℓ.mem (T.constellationPoint q)) with hPFdef
  have hPFset : (PF : Set ConstellationIndex) =
      {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)} := by
    ext q
    simp [hPFdef]
  have hPFcard : PF.card = 6 := by
    rw [← Set.ncard_coe_finset (s := PF), hPFset]
    exact hisg.2.1
  have hdisj : (PF : Set ConstellationIndex).PairwiseDisjoint m6Idx := by
    intro q hq q' hq' hne
    exact m6_disjoint T h hcan hnot hne (by simpa [hPFdef] using hq)
      (by simpa [hPFdef] using hq')
  have hcard12 : (PF.biUnion m6Idx).card = 12 := by
    rw [Finset.card_biUnion hdisj]
    have hsum : ∑ q ∈ PF, (m6Idx q).card = ∑ _q ∈ PF, 2 :=
      Finset.sum_congr rfl (fun q _ => m6Idx_card q)
    rw [hsum, Finset.sum_const, hPFcard]
    norm_num
  have hle9 : (PF.biUnion m6Idx).card ≤ 9 := by
    calc (PF.biUnion m6Idx).card ≤ Fintype.card (TrisectorLabel × TrisectorLabel) :=
          Finset.card_le_univ _
      _ = 9 := by simp [Fintype.card_prod, ZMod.card]
  omega

/-- **`|guideLines| ≤ 9`, unconditionally.**  This is the hard half of
`guideLines_card`, and it needs no diagonal-pair exclusion at all. -/
theorem m6_guideLines_ncard_le_nine (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) : T.guideLines.ncard ≤ 9 := by
  classical
  have hex : ∀ x : {ℓ : Line E // ℓ ∈ T.guideLines},
      ∃ p : TrisectorLabel × TrisectorLabel, (x : Line E) = m6Canon (o := o) T h p :=
    fun x => m6_guide_mem_nine T h x.2
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (by rw [hf x, hf y, hxy])
  have hle : T.guideLines.ncard ≤ Nat.card (TrisectorLabel × TrisectorLabel) := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective f hinj
  have h9 : Nat.card (TrisectorLabel × TrisectorLabel) = 9 := by
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_prod, ZMod.card]
  rw [h9] at hle
  exact hle

/-- **At most three guide lines are parallel to a fixed vector.**  The upper bound of
`guideLines_direction_card`, also unconditional. -/
theorem m6_direction_le_three (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (v : E) :
    {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard ≤ 3 := by
  classical
  set S : Set (Line E) := {ℓ ∈ T.guideLines | Parallel v ℓ.direction} with hS
  rcases S.eq_empty_or_nonempty with hemp | hne
  · rw [hemp]
    simp
  obtain ⟨ℓ₀, hℓ₀⟩ := hne
  have hv : v ≠ 0 := by
    rintro rfl
    obtain ⟨r, hr⟩ := hℓ₀.2
    exact ℓ₀.direction_ne_zero (by rw [hr, smul_zero])
  set x₀ : S := ⟨ℓ₀, hℓ₀⟩ with hx₀
  have hex : ∀ x : S, ∃ p : TrisectorLabel × TrisectorLabel,
      (x : Line E) = m6Canon (o := o) T h p :=
    fun x => m6_guide_mem_nine T h x.2.1
  choose f hf using hex
  have hdir : ∀ x : S, Parallel v (m3pSide T (f x).2) := by
    intro x
    have hpar : Parallel v ((x : Line E).direction) := x.2.2
    have hp : Parallel ((x : Line E).direction) (m3pSide T (f x).2) := by
      rw [hf x]
      exact parallel_comm (m4Side_ne T (f x).2)
        (m6Canon (o := o) T h (f x)).direction_ne_zero (m6Canon_direction_par T h (f x))
    exact hpar.trans hp
  have hconst : ∀ x : S, (f x).2 = (f x₀).2 := by
    intro x
    by_contra hc
    have hpar : Parallel (m3pSide T (f x).2) (m3pSide T (f x₀).2) :=
      (parallel_comm hv (m4Side_ne T (f x).2) (hdir x)).trans (hdir x₀)
    exact m4_side_not_parallel T (fun hh => hc hh) hpar
  have hinjf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (by rw [hf x, hf y, hxy])
  have hinj : Function.Injective
      (fun x : S => (⟨f x, hconst x⟩ :
        {p : TrisectorLabel × TrisectorLabel // p.2 = (f x₀).2})) := by
    intro x y hxy
    have h1 : f x = f y := by simpa using hxy
    exact hinjf h1
  have hcard3 : ({p : TrisectorLabel × TrisectorLabel | p.2 = (f x₀).2}).ncard = 3 := by
    have heq : {p : TrisectorLabel × TrisectorLabel | p.2 = (f x₀).2}
        = Set.univ ×ˢ ({((f x₀).2)} : Set TrisectorLabel) := by
      ext p
      simp
    rw [heq, Set.ncard_prod, Set.ncard_univ, Set.ncard_singleton, mul_one,
      Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have h2 : Nat.card S ≤
      Nat.card {p : TrisectorLabel × TrisectorLabel // p.2 = (f x₀).2} :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_coe_set_eq] at h2
  have h3 : Nat.card {p : TrisectorLabel × TrisectorLabel // p.2 = (f x₀).2}
      = ({p : TrisectorLabel × TrisectorLabel | p.2 = (f x₀).2}).ncard := rfl
  rw [h3, hcard3] at h2
  exact h2

end XamboMorley.M6
