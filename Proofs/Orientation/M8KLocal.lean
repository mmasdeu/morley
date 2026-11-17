import XamboMorleyBase

/-!
# The sum-one area closed form for `tricolor_orientation` (member m8, sixth run)

This file proves, axiom-clean, the **direct key identity** of
`.ultramath/smwh7aexl/m4/M4B_DERIVATION.md` §4:

`(starRingEnd ℂ) (Ap a b) * Bp a b - Ap a b * (starRingEnd ℂ) (Bp a b) = 2 * I * Lamab a b`

equivalently `Im(conj(Ap)·Bp) = Lamab a b`, where `Ap`, `Bp` are the half-angle forms of
`g - r = X·Ap`, `b - r = X·Bp`, i.e. the oriented area of the sum-one tricolor triangle.

The proof never runs `ring` on the difference of the two raw quotients (which needs >14 GB).
Instead it clears the denominators in four structured stages:

* `Ap nf`, `Bp nf` — single-denominator forms with the correction `W = Zl a b` kept opaque
  and the shape relation `P1 = -(a · Usqc b)` replacing the `tc` denominators;
* `conj(Ap)·Bp = -(Y)/(Dr)` with `Dr` a **real** polynomial;
* `Y · Dn = NN` with `Dn` real, `NN` a polynomial (only `W·Dn`, `Wc·Dn` and `W·Wc·Dn` are used);
* `Im(NN) = -target` — a pure polynomial identity in `ℝ`, split into six small `ring` calls.

Prefix: `M8K`.  Nothing here is imported from another member's directory.
-/

noncomputable section
namespace M8K

open Complex

/-! ### Half-angle units -/

def Usq (a : ℝ) : ℂ := (((1 - a^2 : ℝ)) : ℂ) + (((2 * a : ℝ)) : ℂ) * Complex.I
def Usqc (a : ℝ) : ℂ := (((1 - a^2 : ℝ)) : ℂ) - (((2 * a : ℝ)) : ℂ) * Complex.I
def U6 (a : ℝ) : ℂ := (((1 - 15*a^2 + 15*a^4 - a^6 : ℝ)) : ℂ)
  + (((6*a - 20*a^3 + 6*a^5 : ℝ)) : ℂ) * Complex.I
def U6c (a : ℝ) : ℂ := (((1 - 15*a^2 + 15*a^4 - a^6 : ℝ)) : ℂ)
  - (((6*a - 20*a^3 + 6*a^5 : ℝ)) : ℂ) * Complex.I

lemma Usq_mul (x : ℝ) : Usq x * Usqc x = ((((1+x^2)^2 : ℝ)) : ℂ) := by
  apply Complex.ext
  · simp only [Usq, Usqc, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    push_cast
    ring
  · simp only [Usq, Usqc, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    push_cast
    ring

lemma U6_mul (x : ℝ) : U6 x * U6c x = ((((1+x^2)^6 : ℝ)) : ℂ) := by
  apply Complex.ext
  · simp only [U6, U6c, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    push_cast
    ring
  · simp only [U6, U6c, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    push_cast
    ring

lemma Usq_ne (x : ℝ) : Usq x ≠ 0 := by
  intro h
  have h0 : ((((1+x^2)^2 : ℝ)) : ℂ) = 0 := by rw [← Usq_mul, h, zero_mul]
  have h1 : (1+x^2)^2 = 0 := by exact_mod_cast h0
  have h2 : (0:ℝ) < 1+x^2 := by positivity
  exact absurd h1 (ne_of_gt (pow_pos h2 2))

lemma Usqc_ne (x : ℝ) : Usqc x ≠ 0 := by
  intro h
  have h0 : ((((1+x^2)^2 : ℝ)) : ℂ) = 0 := by rw [← Usq_mul, h, mul_zero]
  have h1 : (1+x^2)^2 = 0 := by exact_mod_cast h0
  have h2 : (0:ℝ) < 1+x^2 := by positivity
  exact absurd h1 (ne_of_gt (pow_pos h2 2))

lemma U6_ne (x : ℝ) : U6 x ≠ 0 := by
  intro h
  have h0 : ((((1+x^2)^6 : ℝ)) : ℂ) = 0 := by rw [← U6_mul, h, zero_mul]
  have h1 : (1+x^2)^6 = 0 := by exact_mod_cast h0
  have h2 : (0:ℝ) < 1+x^2 := by positivity
  exact absurd h1 (ne_of_gt (pow_pos h2 6))

lemma U6c_ne (x : ℝ) : U6c x ≠ 0 := by
  intro h
  have h0 : ((((1+x^2)^6 : ℝ)) : ℂ) = 0 := by rw [← U6_mul, h, mul_zero]
  have h1 : (1+x^2)^6 = 0 := by exact_mod_cast h0
  have h2 : (0:ℝ) < 1+x^2 := by positivity
  exact absurd h1 (ne_of_gt (pow_pos h2 6))

/-! ### The sum-one vertex coefficients -/

def Z1 (a b : ℝ) : ℂ := -Usq a*(b:ℂ)/((a:ℂ)*Usqc b)
def Z2 (a b : ℝ) : ℂ := -(((a:ℂ)+(b:ℂ))*((a:ℂ)*(b:ℂ)-1))/((b:ℂ)*Usq a)
def Z3 (a b : ℝ) : ℂ := -(a:ℂ)*Usqc b/(((a:ℂ)+(b:ℂ))*((a:ℂ)*(b:ℂ)-1))
def Zl (a b : ℝ) : ℂ := U6 a*(b:ℂ)*(((3*b^2-1 : ℝ)):ℂ)*(((b^2-3 : ℝ)):ℂ)
  /(U6c b*(a:ℂ)*(((3*a^2-1 : ℝ)):ℂ)*(((a^2-3 : ℝ)):ℂ))

def Z1c (a b : ℝ) : ℂ := -Usqc a*(b:ℂ)/((a:ℂ)*Usq b)
def Z2c (a b : ℝ) : ℂ := -(((a:ℂ)+(b:ℂ))*((a:ℂ)*(b:ℂ)-1))/((b:ℂ)*Usqc a)
def Z3c (a b : ℝ) : ℂ := -(a:ℂ)*Usq b/(((a:ℂ)+(b:ℂ))*((a:ℂ)*(b:ℂ)-1))
def Zlc (a b : ℝ) : ℂ := U6c a*(b:ℂ)*(((3*b^2-1 : ℝ)):ℂ)*(((b^2-3 : ℝ)):ℂ)
  /(U6 b*(a:ℂ)*(((3*a^2-1 : ℝ)):ℂ)*(((a^2-3 : ℝ)):ℂ))

/-- `Ap` of the derivation: `g - r = X · Ap`. -/
def Ap (a b : ℝ) : ℂ := Zl a b*(Z2 a b - 1) - Z1 a b
/-- `Bp` of the derivation: `b - r = X · Bp`. -/
def Bp (a b : ℝ) : ℂ := 1 - Z1 a b - Z3 a b - Zl a b*Z3 a b
def Apc (a b : ℝ) : ℂ := Zlc a b*(Z2c a b - 1) - Z1c a b
def Bpc (a b : ℝ) : ℂ := 1 - Z1c a b - Z3c a b - Zlc a b*Z3c a b

lemma conj_Usq (a : ℝ) : (starRingEnd ℂ) (Usq a) = Usqc a := by
  simp only [Usq, Usqc, map_add, map_sub, map_mul, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  ring
lemma conj_Usqc (a : ℝ) : (starRingEnd ℂ) (Usqc a) = Usq a := by
  simp only [Usq, Usqc, map_add, map_sub, map_mul, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  ring
lemma conj_U6 (a : ℝ) : (starRingEnd ℂ) (U6 a) = U6c a := by
  simp only [U6, U6c, map_add, map_sub, map_mul, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  ring
lemma conj_U6c (a : ℝ) : (starRingEnd ℂ) (U6c a) = U6 a := by
  simp only [U6, U6c, map_add, map_sub, map_mul, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal]
  ring

lemma conj_Z1 (a b : ℝ) : (starRingEnd ℂ) (Z1 a b) = Z1c a b := by
  simp only [Z1, Z1c, map_mul, map_sub, map_add, map_one, map_div₀, map_neg,
    map_ofNat, Complex.conj_ofReal, conj_Usq, conj_Usqc]
lemma conj_Z2 (a b : ℝ) : (starRingEnd ℂ) (Z2 a b) = Z2c a b := by
  simp only [Z2, Z2c, map_mul, map_sub, map_add, map_one, map_div₀, map_neg,
    map_ofNat, Complex.conj_ofReal, conj_Usq, conj_Usqc]
lemma conj_Z3 (a b : ℝ) : (starRingEnd ℂ) (Z3 a b) = Z3c a b := by
  simp only [Z3, Z3c, map_mul, map_sub, map_add, map_one, map_div₀, map_neg,
    map_ofNat, Complex.conj_ofReal, conj_Usq, conj_Usqc]
lemma conj_Zl (a b : ℝ) : (starRingEnd ℂ) (Zl a b) = Zlc a b := by
  simp only [Zl, Zlc, map_mul, map_sub, map_add, map_one, map_div₀, map_neg,
    map_ofNat, Complex.conj_ofReal, conj_U6, conj_U6c]

lemma conj_Ap (a b : ℝ) : (starRingEnd ℂ) (Ap a b) = Apc a b := by
  simp only [Ap, Apc, map_mul, map_sub, map_add, map_one, map_neg, conj_Z1, conj_Z2, conj_Z3,
    conj_Zl]
lemma conj_Bp (a b : ℝ) : (starRingEnd ℂ) (Bp a b) = Bpc a b := by
  simp only [Bp, Bpc, map_mul, map_sub, map_add, map_one, map_neg, conj_Z1, conj_Z2, conj_Z3,
    conj_Zl]

/-! ### The shape relation and the reduced variables -/

/-- `m = (a+b)(ab-1)`: the numerator of `Z3`. -/
def mm (a b : ℝ) : ℝ := (a + b) * (a * b - 1)
/-- `P1 = m + b·Usq a`.  It satisfies `P1 = -(a·Usqc b)` and `P1·P2 = a²(1+b²)²`. -/
def P1 (a b : ℝ) : ℂ := ((mm a b : ℝ) : ℂ) + (b:ℂ) * Usq a
/-- `P2 = conj P1 = m + b·Usqc a`. -/
def P2 (a b : ℝ) : ℂ := ((mm a b : ℝ) : ℂ) + (b:ℂ) * Usqc a

lemma P1_rel (a b : ℝ) : P1 a b = -((a:ℂ) * Usqc b) := by
  simp only [P1, mm, Usq, Usqc]
  push_cast
  ring

lemma P2_rel (a b : ℝ) : P2 a b = -((a:ℂ) * Usq b) := by
  simp only [P2, mm, Usq, Usqc]
  push_cast
  ring

lemma conj_P1 (a b : ℝ) : (starRingEnd ℂ) (P1 a b) = P2 a b := by
  rw [P1_rel, P2_rel, map_neg, map_mul, Complex.conj_ofReal, conj_Usqc]

lemma P1_ne (a b : ℝ) (ha : a ≠ 0) : P1 a b ≠ 0 := by
  rw [P1_rel]
  exact neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) (Usqc_ne b))

lemma P2_ne (a b : ℝ) (ha : a ≠ 0) : P2 a b ≠ 0 := by
  rw [P2_rel]
  exact neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) (Usq_ne b))

lemma P1P2 (a b : ℝ) : P1 a b * P2 a b = (((a^2 * (1+b^2)^2 : ℝ)) : ℂ) := by
  rw [P1_rel, P2_rel, neg_mul_neg]
  have h : ((a:ℂ) * Usqc b) * ((a:ℂ) * Usq b) = ((a:ℂ) * (a:ℂ)) * (Usqc b * Usq b) := by
    ring
  rw [h, mul_comm (Usqc b) (Usq b), Usq_mul]
  push_cast
  ring

/-! ### Reduced variables and the two single-denominator normal forms

`W = Zl a b` and `Wc = Zlc a b` are kept as *parameters* here, so that `field_simp` never
clears the sixfold denominators hidden inside `Zl`. -/

/-- `Ap` with the correction factor `W` as a parameter. -/
def ApW (W : ℂ) (a b : ℝ) : ℂ := W*(Z2 a b - 1) - Z1 a b
/-- `Bp` with the correction factor `W` as a parameter. -/
def BpW (W : ℂ) (a b : ℝ) : ℂ := 1 - Z1 a b - Z3 a b - W*Z3 a b
/-- `conj Ap` with `Wc = conj W` as a parameter. -/
def ApWc (Wc : ℂ) (a b : ℝ) : ℂ := Wc*(Z2c a b - 1) - Z1c a b
/-- `conj Bp` with `Wc = conj W` as a parameter. -/
def BpWc (Wc : ℂ) (a b : ℝ) : ℂ := 1 - Z1c a b - Z3c a b - Wc*Z3c a b

lemma Ap_eq (a b : ℝ) : Ap a b = ApW (Zl a b) a b := rfl
lemma Bp_eq (a b : ℝ) : Bp a b = BpW (Zl a b) a b := rfl
lemma Apc_eq (a b : ℝ) : Apc a b = ApWc (Zlc a b) a b := rfl
lemma Bpc_eq (a b : ℝ) : Bpc a b = BpWc (Zlc a b) a b := rfl
lemma conj_Ap' (a b : ℝ) : (starRingEnd ℂ) (Ap a b) = ApWc (Zlc a b) a b := by
  rw [conj_Ap, Apc_eq]
lemma conj_Bp' (a b : ℝ) : (starRingEnd ℂ) (Bp a b) = BpWc (Zlc a b) a b := by
  rw [conj_Bp, Bpc_eq]

/-- `P1 - b·Usq a = m`. -/
lemma P1_sub (a b : ℝ) : P1 a b - (b:ℂ) * Usq a = ((mm a b : ℝ) : ℂ) := by
  simp only [P1]
  ring

lemma Z2m1 (a b : ℝ) (hb : b ≠ 0) : Z2 a b - 1 = -(P1 a b)/((b:ℂ) * Usq a) := by
  have h1 : (b:ℂ) ≠ 0 := by exact_mod_cast hb
  have h2 : Usq a ≠ 0 := Usq_ne a
  simp only [Z2, P1, mm]
  field_simp
  push_cast
  ring

lemma Z2cm1 (a b : ℝ) (hb : b ≠ 0) : Z2c a b - 1 = -(P2 a b)/((b:ℂ) * Usqc a) := by
  have h1 : (b:ℂ) ≠ 0 := by exact_mod_cast hb
  have h2 : Usqc a ≠ 0 := Usqc_ne a
  simp only [Z2c, P2, mm]
  field_simp
  push_cast
  ring

lemma Z1f (a b : ℝ) (ha : a ≠ 0) : Z1 a b = (b:ℂ) * Usq a / P1 a b := by
  have h1 : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have h2 : Usqc b ≠ 0 := Usqc_ne b
  have h3 : P1 a b ≠ 0 := P1_ne a b ha
  simp only [Z1]
  rw [P1_rel]
  field_simp

lemma Z1cf (a b : ℝ) (ha : a ≠ 0) : Z1c a b = (b:ℂ) * Usqc a / P2 a b := by
  have h1 : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have h2 : Usq b ≠ 0 := Usq_ne b
  have h3 : P2 a b ≠ 0 := P2_ne a b ha
  simp only [Z1c]
  rw [P2_rel]
  field_simp

lemma Z3f (a b : ℝ) : Z3 a b = P1 a b / ((mm a b : ℝ) : ℂ) := by
  rw [P1_rel]
  simp only [Z3, mm, Usq, Usqc]
  push_cast
  ring

lemma Z3cf (a b : ℝ) : Z3c a b = P2 a b / ((mm a b : ℝ) : ℂ) := by
  rw [P2_rel]
  simp only [Z3c, mm, Usq, Usqc]
  push_cast
  ring

/-- **`Ap` normal form.** -/
lemma ApW_nf (W : ℂ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ApW W a b * (P1 a b * (b:ℂ) * Usq a) = -(W * (P1 a b)^2 + (b:ℂ)^2 * (Usq a)^2) := by
  have hb' : (b:ℂ) ≠ 0 := by exact_mod_cast hb
  have h2 : Usq a ≠ 0 := Usq_ne a
  have hP1 : P1 a b ≠ 0 := P1_ne a b ha
  simp only [ApW]
  rw [Z2m1 a b hb, Z1f a b ha]
  field_simp
  ring

/-- **`conj Ap` normal form.** -/
lemma ApWc_nf (Wc : ℂ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ApWc Wc a b * (P2 a b * (b:ℂ) * Usqc a) = -(Wc * (P2 a b)^2 + (b:ℂ)^2 * (Usqc a)^2) := by
  have hb' : (b:ℂ) ≠ 0 := by exact_mod_cast hb
  have h2 : Usqc a ≠ 0 := Usqc_ne a
  have hP2 : P2 a b ≠ 0 := P2_ne a b ha
  simp only [ApWc]
  rw [Z2cm1 a b hb, Z1cf a b ha]
  field_simp
  ring

/-- **`Bp` normal form.** -/
lemma BpW_nf (W : ℂ) (a b : ℝ) (ha : a ≠ 0) (hm : mm a b ≠ 0) :
    BpW W a b * (P1 a b * ((mm a b : ℝ) : ℂ)) = ((mm a b : ℝ) : ℂ)^2 - (1 + W) * (P1 a b)^2 := by
  have hmc : ((mm a b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm
  have hP1 : P1 a b ≠ 0 := P1_ne a b ha
  have hsub := P1_sub a b
  have hsub' : P1 a b - (b:ℂ) * Usq a ≠ 0 := by rw [hsub]; exact hmc
  simp only [BpW]
  rw [Z1f a b ha, Z3f a b, ← hsub]
  field_simp
  ring

/-! ### The real clearing factors `Dr`, `Dn`, `S1`, `kap`, `kap2` -/

/-- `S1 = a²(3a²-1)²(a²-3)²`: the squared `Zl` denominator. -/
def S1 (a : ℝ) : ℝ := a^2 * (3*a^2-1)^2 * (a^2-3)^2
/-- `Dn = (1+b²)^6 S1 = U6 b · U6c b · S1`: the real clearing factor for `Zl`. -/
def Dn (a b : ℝ) : ℝ := (1+b^2)^6 * S1 a
/-- `kap = a b (3a²-1)(3b²-1)(a²-3)(b²-3)`: the `Zl · Dn` numerator. -/
def kap (a b : ℝ) : ℝ := a*b*(3*a^2-1)*(3*b^2-1)*(a^2-3)*(b^2-3)
/-- `kap2 = (1+a²)^6 b²(3b²-1)²(b²-3)²`: the `Zl · Zlc · Dn` numerator. -/
def kap2 (a b : ℝ) : ℝ := (1+a^2)^6 * b^2 * (3*b^2-1)^2 * (b^2-3)^2
/-- `Dr = a² b (1+a²)²(1+b²)² m`: the real denominator of `conj(Ap)·Bp`. -/
def Dr (a b : ℝ) : ℝ := a^2 * b * (1+a^2)^2 * (1+b^2)^2 * mm a b
/-- The numerator of `Zl` apart from `U6 a`. -/
def Nb (b : ℝ) : ℂ := (b:ℂ) * (((3*b^2-1 : ℝ)):ℂ) * (((b^2-3 : ℝ)):ℂ)
/-- The denominator of `Zl` apart from `U6c b`. -/
def Da (a : ℝ) : ℂ := (a:ℂ) * (((3*a^2-1 : ℝ)):ℂ) * (((a^2-3 : ℝ)):ℂ)

/-- The polynomial quartic of §4. -/
def Pab (a b : ℝ) : ℝ :=
  9*a^4*b^4 - 14*a^4*b^2 + 9*a^4 - 32*a^3*b^3 + 32*a^3*b - 14*a^2*b^4
  + 36*a^2*b^2 - 14*a^2 + 32*a*b^3 - 32*a*b + 9*b^4 - 14*b^2 + 9

/-- The `Λ` of §4: the imaginary part of `conj(Ap)·Bp`. -/
def Lamab (a b : ℝ) : ℝ :=
  6*b*(a+b)*(1+a^2)^2*(a*b-1)*Pab a b/(a*(a^2-3)^2*(3*a^2-1)^2*(1+b^2)^4)

/-- `Y = (Wc·P2² + b²·Usqc a²)·Usq a·(m² - (1+W)P1²)`, so that `conj(Ap)·Bp = -Y/Dr`. -/
def YC (a b : ℝ) : ℂ :=
  (Zlc a b * (P2 a b)^2 + (b:ℂ)^2 * (Usqc a)^2) * Usq a
    * (((mm a b : ℝ) : ℂ)^2 - (1 + Zl a b) * (P1 a b)^2)

/-- `NN = Y·Dn`, a polynomial: the whole numerator of the area computation. -/
def NN (a b : ℝ) : ℂ :=
    ((((mm a b)^2 * kap a b : ℝ)) : ℂ) * (Usq a * U6c a * U6c b * (P2 a b)^2)
  + ((((mm a b)^2 * b^2 * Dn a b : ℝ)) : ℂ) * (Usq a * (Usqc a)^2)
  - (((kap a b : ℝ)) : ℂ) * (Usq a * (P1 a b)^2 * U6c a * U6c b * (P2 a b)^2)
  - (((b^2 * Dn a b : ℝ)) : ℂ) * (Usq a * (P1 a b)^2 * (Usqc a)^2)
  - (((kap2 a b : ℝ)) : ℂ) * (Usq a * (P1 a b)^2 * (P2 a b)^2)
  - (((kap a b * b^2 : ℝ)) : ℂ) * (Usq a * (P1 a b)^2 * (Usqc a)^2 * U6 a * U6 b)

lemma Zl_eq (a b : ℝ) : Zl a b = U6 a * Nb b / (U6c b * Da a) := by
  simp only [Zl, Nb, Da]
  ring
lemma Zlc_eq (a b : ℝ) : Zlc a b = U6c a * Nb b / (U6 b * Da a) := by
  simp only [Zlc, Nb, Da]
  ring

lemma Dn_split (a b : ℝ) : ((Dn a b : ℝ) : ℂ) = U6 b * U6c b * ((S1 a : ℝ) : ℂ) := by
  rw [show ((Dn a b : ℝ) : ℂ) = (((1+b^2)^6 : ℝ) : ℂ) * ((S1 a : ℝ) : ℂ) from by
        simp only [Dn]; push_cast; ring,
      ← U6_mul b]

/-- `Zl · Dn = kap · U6 a · U6 b`. -/
lemma ZlDn (a b : ℝ) (ha : a ≠ 0) (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0) :
    Zl a b * ((Dn a b : ℝ) : ℂ) = ((kap a b : ℝ) : ℂ) * U6 a * U6 b := by
  have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have h31' : (((3*a^2-1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h31
  have h13' : (((a^2-3 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h13
  have hU6cb : U6c b ≠ 0 := U6c_ne b
  rw [Zl_eq, Dn_split]
  simp only [kap, S1, Nb, Da]
  field_simp
  push_cast
  ring

/-- `Zlc · Dn = kap · U6c a · U6c b`. -/
lemma ZlcDn (a b : ℝ) (ha : a ≠ 0) (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0) :
    Zlc a b * ((Dn a b : ℝ) : ℂ) = ((kap a b : ℝ) : ℂ) * U6c a * U6c b := by
  have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have h31' : (((3*a^2-1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h31
  have h13' : (((a^2-3 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h13
  have hU6b : U6 b ≠ 0 := U6_ne b
  rw [Zlc_eq, Dn_split]
  simp only [kap, S1, Nb, Da]
  field_simp
  push_cast
  ring

/-- `Zl · Zlc · Dn = kap2`. -/
lemma ZlZlcDn (a b : ℝ) (ha : a ≠ 0) (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0) :
    Zl a b * Zlc a b * ((Dn a b : ℝ) : ℂ) = ((kap2 a b : ℝ) : ℂ) := by
  have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have h31' : (((3*a^2-1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h31
  have h13' : (((a^2-3 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h13
  have hU6cb : U6c b ≠ 0 := U6c_ne b
  have hU6b : U6 b ≠ 0 := U6_ne b
  have hU6a : U6 a ≠ 0 := U6_ne a
  have hU6ca : U6c a = (((1+a^2)^6 : ℝ) : ℂ) / U6 a := by
    rw [eq_div_iff hU6a, mul_comm]; exact U6_mul a
  have hZlc' : Zlc a b = (((1+a^2)^6 : ℝ) : ℂ) * Nb b / (U6 a * U6 b * Da a) := by
    rw [Zlc_eq, hU6ca]
    field_simp
  rw [Zl_eq, hZlc', Dn_split]
  simp only [kap2, S1, Nb, Da]
  field_simp
  push_cast
  ring


set_option maxHeartbeats 4000000 in
/-- **The pure polynomial identity.**  `Im(NN)` is minus the closed form of §4, with the
common factor `6 a³ b² (a+b)² (ab-1)² (1+a²)⁴ (1+b²)⁴`. -/
lemma im_NN (a b : ℝ) :
    (NN a b).im =
      -(6*a^3*b^2*(a+b)^2*(a*b-1)^2*(1+a^2)^4*(1+b^2)^4*Pab a b) := by
  simp only [NN, Pab, mm, kap, kap2, Dn, S1, P1, P2, Usq, Usqc, U6, U6c,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    pow_two]
  push_cast
  ring


/-- **`conj(Ap)·Bp · Dr = -Y`.**  The product with the real clearing factor `Dr` is minus the
polynomial expression `Y`; this is where `P1·P2 = a²(1+b²)²` and `Usq a·Usqc a = (1+a²)²`
are used. -/
lemma prodW (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hm : mm a b ≠ 0) :
    (starRingEnd ℂ) (Ap a b) * Bp a b * ((Dr a b : ℝ) : ℂ) = -(YC a b) := by
  have hP2 : P2 a b ≠ 0 := P2_ne a b ha
  have hmc : ((mm a b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm
  have hDr : ((Dr a b : ℝ) : ℂ)
      = P1 a b * P2 a b * ((b:ℂ) * (Usq a * Usqc a)) * ((mm a b : ℝ) : ℂ) := by
    rw [P1P2, Usq_mul]
    simp only [Dr]
    push_cast
    ring
  have h1 := ApWc_nf (Zlc a b) a b ha hb
  have h2 := BpW_nf (Zl a b) a b ha hm
  rw [conj_Ap', Bp_eq, hDr]
  rw [show ApWc (Zlc a b) a b * BpW (Zl a b) a b
        * (P1 a b * P2 a b * ((b:ℂ) * (Usq a * Usqc a)) * ((mm a b : ℝ) : ℂ))
      = (ApWc (Zlc a b) a b * (P2 a b * (b:ℂ) * Usqc a))
        * (BpW (Zl a b) a b * (P1 a b * ((mm a b : ℝ) : ℂ))) * Usq a from by ring,
    h1, h2]
  simp only [YC]
  ring

/-- **`Y · Dn = NN`.**  Clearing the `Zl`/`Zlc` denominators of `Y` with the real factor `Dn`
leaves the polynomial `NN`.  Uses only `Zl·Dn`, `Zlc·Dn` and `Zl·Zlc·Dn`. -/
lemma YDn (a b : ℝ) (ha : a ≠ 0) (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0) :
    YC a b * ((Dn a b : ℝ) : ℂ) = NN a b := by
  have hW := ZlDn a b ha h31 h13
  have hWc := ZlcDn a b ha h31 h13
  have hWW := ZlZlcDn a b ha h31 h13
  rw [show YC a b * ((Dn a b : ℝ) : ℂ)
      = (Zlc a b * ((Dn a b : ℝ) : ℂ)) * (P2 a b)^2 * Usq a * (((mm a b : ℝ) : ℂ)^2)
        + (b:ℂ)^2 * (Usqc a)^2 * ((Dn a b : ℝ) : ℂ) * Usq a * (((mm a b : ℝ) : ℂ)^2)
        - (Zlc a b * ((Dn a b : ℝ) : ℂ)) * (P2 a b)^2 * Usq a * (P1 a b)^2
        - (b:ℂ)^2 * (Usqc a)^2 * ((Dn a b : ℝ) : ℂ) * Usq a * (P1 a b)^2
        - (Zl a b * Zlc a b * ((Dn a b : ℝ) : ℂ)) * (P2 a b)^2 * Usq a * (P1 a b)^2
        - (Zl a b * ((Dn a b : ℝ) : ℂ)) * (b:ℂ)^2 * (Usqc a)^2 * Usq a * (P1 a b)^2
      from by simp only [YC]; ring]
  rw [hW, hWc, hWW]
  simp only [NN]
  push_cast
  ring

/-- **The area identity.**  `Im(conj(Ap)·Bp) = Λ(a,b)`, the sum-one oriented area. -/
theorem im_key (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hm : mm a b ≠ 0)
    (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0) :
    ((starRingEnd ℂ) (Ap a b) * Bp a b).im = Lamab a b := by
  have hDr : Dr a b ≠ 0 := by
    have hpos : (0:ℝ) < a^2 * (1+a^2)^2 * (1+b^2)^2 := by positivity
    have hbm : b * mm a b ≠ 0 := mul_ne_zero hb hm
    have he : Dr a b = (a^2 * (1+a^2)^2 * (1+b^2)^2) * (b * mm a b) := by
      simp only [Dr]; ring
    rw [he]
    exact mul_ne_zero (ne_of_gt hpos) hbm
  have hDn : Dn a b ≠ 0 := by
    have hs : S1 a ≠ 0 := by
      have h1 : (0:ℝ) < a^2 := by positivity
      have h2 : ((3*a^2-1))^2 ≠ 0 := pow_ne_zero 2 h31
      have h3 : (a^2-3)^2 ≠ 0 := pow_ne_zero 2 h13
      have he : S1 a = a^2 * (3*a^2-1)^2 * (a^2-3)^2 := rfl
      rw [he]
      exact mul_ne_zero (mul_ne_zero (ne_of_gt h1) h2) h3
    have he : Dn a b = (1+b^2)^6 * S1 a := rfl
    rw [he]
    exact mul_ne_zero (pow_ne_zero 6 (by positivity)) hs
  have h1 : ((starRingEnd ℂ) (Ap a b) * Bp a b).im * Dr a b = -((YC a b).im) := by
    have h := congrArg Complex.im (prodW a b ha hb hm)
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im] at h
    simpa only [mul_zero, add_zero, zero_add] using h
  have h2 : (YC a b).im * Dn a b
      = -(6*a^3*b^2*(a+b)^2*(a*b-1)^2*(1+a^2)^4*(1+b^2)^4*Pab a b) := by
    have h := congrArg Complex.im (YDn a b ha h31 h13)
    rw [im_NN] at h
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h
    simpa only [mul_zero, add_zero, zero_add] using h
  have h3 : ((starRingEnd ℂ) (Ap a b) * Bp a b).im * (Dr a b * Dn a b)
      = 6*a^3*b^2*(a+b)^2*(a*b-1)^2*(1+a^2)^4*(1+b^2)^4*Pab a b := by
    linear_combination (Dn a b) * h1 - h2
  have hD : Dr a b * Dn a b ≠ 0 := mul_ne_zero hDr hDn
  have hL : Lamab a b
      = (6*a^3*b^2*(a+b)^2*(a*b-1)^2*(1+a^2)^4*(1+b^2)^4*Pab a b) / (Dr a b * Dn a b) := by
    simp only [Lamab, Dr, Dn, S1, mm]
    field_simp
  rw [hL, eq_div_iff hD]
  exact h3

/-- **The direct key identity** of `M4B_DERIVATION.md` §4: the difference of the two
conjugates is `2 i Λ`, i.e. the oriented area of the sum-one tricolor triangle. -/
theorem key_identity (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hm : mm a b ≠ 0)
    (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0) :
    (starRingEnd ℂ) (Ap a b) * Bp a b - Ap a b * (starRingEnd ℂ) (Bp a b)
      = ((2 * Lamab a b : ℝ) : ℂ) * Complex.I := by
  have h1 : Ap a b * (starRingEnd ℂ) (Bp a b)
      = (starRingEnd ℂ) ((starRingEnd ℂ) (Ap a b) * Bp a b) := by
    rw [map_mul, Complex.conj_conj]
  rw [h1, Complex.sub_conj, im_key a b ha hb hm h31 h13]

/-! ### The sign of the sum-one area -/

lemma cos_half_sq (u : ℝ) : Real.cos u = 2 * Real.cos (u/2)^2 - 1 := by
  have h1 := Real.cos_two_mul (u/2)
  have h2 : (2:ℝ) * (u/2) = u := by ring
  rw [h2] at h1
  exact h1

lemma sin_half (u : ℝ) : Real.sin u = 2 * Real.sin (u/2) * Real.cos (u/2) := by
  have h2 : (2:ℝ) * (u/2) = u := by ring
  conv_lhs => rw [← h2]
  rw [Real.sin_two_mul]

/-- `tan(u/2)·(1 + cos u) = sin u`; holds for every real `u`. -/
lemma tan_half_mul (u : ℝ) : Real.tan (u/2) * (1 + Real.cos u) = Real.sin u := by
  rw [Real.tan_eq_sin_div_cos, cos_half_sq u, sin_half u]
  by_cases hc : Real.cos (u/2) = 0
  · rw [hc]; ring
  · field_simp
    ring

/-- **The sum-one sign product.**  `(a+b)(ab-1)` in terms of the half angles, with
`a = tan(u/2)`, `b = tan(v/2)`. -/
lemma tan_sum_prod (u v : ℝ) (hu : Real.cos (u/2) ≠ 0) (hv : Real.cos (v/2) ≠ 0) :
    (Real.tan (u/2) + Real.tan (v/2)) * (Real.tan (u/2) * Real.tan (v/2) - 1)
      = -Real.sin (u+v)/(2*Real.cos (u/2)^2*Real.cos (v/2)^2) := by
  have euv : u/2 + v/2 = (u+v)/2 := by ring
  have h1 : Real.sin (u+v) = 2 * Real.sin ((u+v)/2) * Real.cos ((u+v)/2) := by
    have h2 : (2:ℝ) * ((u+v)/2) = u+v := by ring
    conv_lhs => rw [← h2]
    rw [Real.sin_two_mul]
  have h2 : Real.sin ((u+v)/2)
      = Real.sin (u/2)*Real.cos (v/2) + Real.cos (u/2)*Real.sin (v/2) := by
    rw [← euv, Real.sin_add]
  have h3 : Real.cos ((u+v)/2)
      = Real.cos (u/2)*Real.cos (v/2) - Real.sin (u/2)*Real.sin (v/2) := by
    rw [← euv, Real.cos_add]
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, h1, h2, h3]
  field_simp
  ring

/-- Factorisation of `Λ` into a positive factor, the sign-carrying product and `Pab`. -/
lemma Lamab_fac (a b : ℝ) (ha : a ≠ 0) (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0) :
    Lamab a b
      = (6*(1+a^2)^2/((a^2-3)^2*(3*a^2-1)^2*(1+b^2)^4)) * (b*(a+b)*(a*b-1)/a) * Pab a b := by
  have hb' : (1+b^2)^4 ≠ 0 := by positivity
  have h31' : (3*a^2-1)^2 ≠ 0 := pow_ne_zero 2 h31
  have h13' : (a^2-3)^2 ≠ 0 := pow_ne_zero 2 h13
  simp only [Lamab]
  field_simp

/-- **The sign reduction.**  On the nondegenerate half-angle domain the sign of the
sum-one area `Λ` is the sign of `a·b·(a+b)(ab-1)`. -/
theorem Lamab_pos_iff (a b : ℝ) (ha : a ≠ 0) (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0)
    (hP : 0 < Pab a b) : 0 < Lamab a b ↔ 0 < a*b*(a+b)*(a*b-1) := by
  rw [Lamab_fac a b ha h31 h13]
  have hC : 0 < 6*(1+a^2)^2/((a^2-3)^2*(3*a^2-1)^2*(1+b^2)^4) := by positivity
  rw [mul_assoc, mul_pos_iff_of_pos_left hC, mul_pos_iff_of_pos_right hP]
  have hsq : (0:ℝ) < a^2 := by positivity
  have e : b*(a+b)*(a*b-1)/a = a*b*(a+b)*(a*b-1)/a^2 := by
    field_simp
  rw [e, div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, hneg⟩)
    · exact h
    · nlinarith
  · intro h; exact Or.inl ⟨h, hsq⟩

/-- **The sign of the sum-one area in terms of the half angles.**
With `a = tan(u/2)`, `b = tan(v/2)`, the area is positive iff `-(sin u · sin v · sin(u+v))`
is positive.  For the tricolor labels `sin(u+v) = -σ sin w`, giving §6's table. -/
theorem Lamab_pos_iff_sin (u v : ℝ) (hu : Real.cos (u/2) ≠ 0) (hv : Real.cos (v/2) ≠ 0)
    (ha : Real.tan (u/2) ≠ 0) (h31 : 3*(Real.tan (u/2))^2 - 1 ≠ 0)
    (h13 : (Real.tan (u/2))^2 - 3 ≠ 0)
    (hP : 0 < Pab (Real.tan (u/2)) (Real.tan (v/2))) :
    0 < Lamab (Real.tan (u/2)) (Real.tan (v/2)) ↔
      0 < -(Real.sin u * Real.sin v * Real.sin (u+v)) := by
  have hpu : (0:ℝ) < 1 + Real.cos u := by
    have h := pow_pos (abs_pos.mpr hu) 2
    rw [cos_half_sq u]; nlinarith [sq_abs (Real.cos (u/2))]
  have hpv : (0:ℝ) < 1 + Real.cos v := by
    have h := pow_pos (abs_pos.mpr hv) 2
    rw [cos_half_sq v]; nlinarith [sq_abs (Real.cos (v/2))]
  have hpc : (0:ℝ) < 2*Real.cos (u/2)^2*Real.cos (v/2)^2 := by positivity
  have hae : Real.tan (u/2) = Real.sin u/(1 + Real.cos u) := by
    rw [eq_div_iff (ne_of_gt hpu)]; exact tan_half_mul u
  have hbe : Real.tan (v/2) = Real.sin v/(1 + Real.cos v) := by
    rw [eq_div_iff (ne_of_gt hpv)]; exact tan_half_mul v
  have hk := tan_sum_prod u v hu hv
  rw [Lamab_pos_iff (Real.tan (u/2)) (Real.tan (v/2)) ha h31 h13 hP]
  have he : Real.tan (u/2) * Real.tan (v/2) * (Real.tan (u/2) + Real.tan (v/2))
        * (Real.tan (u/2) * Real.tan (v/2) - 1)
      = (Real.sin u * Real.sin v * (-(Real.sin (u+v))))
          / ((1 + Real.cos u) * (1 + Real.cos v) * (2*Real.cos (u/2)^2*Real.cos (v/2)^2)) := by
    rw [show Real.tan (u/2) * Real.tan (v/2) * (Real.tan (u/2) + Real.tan (v/2))
          * (Real.tan (u/2) * Real.tan (v/2) - 1)
        = Real.tan (u/2) * Real.tan (v/2)
          * ((Real.tan (u/2) + Real.tan (v/2)) * (Real.tan (u/2) * Real.tan (v/2) - 1))
        from by ring]
    rw [hk, hae, hbe]
    field_simp
  rw [he, div_pos_iff_of_pos_right (by positivity)]
  rw [show Real.sin u * Real.sin v * (-(Real.sin (u+v)))
      = -(Real.sin u * Real.sin v * Real.sin (u+v)) by ring]


/-! ### Positivity of the quartic `Pab` (the orientation polynomial, `M4B_Algebra`) -/

lemma Pab_form2' (a b X T : ℝ) (hX : X = (a+b)^2) (hT : T = a*b) :
    Pab a b = (3*X - (14*T^2 + 4*T + 14)/6)^2
      + (32/9)*(T+1)^2*(T^2 - 4*T + 1) := by
  subst hX; subst hT; simp only [Pab]; ring

lemma Pab_form3' (a b Y T : ℝ) (hY : Y = (a-b)^2) (hT : T = a*b) :
    Pab a b = 9*Y^2 + (-2*(7*T^2 - 34*T + 7))*Y + (T-3)^2*(3*T-1)^2 := by
  subst hY; subst hT; simp only [Pab]; ring

lemma Pab_nonneg (a b : ℝ) : 0 ≤ Pab a b := by
  have hY : (0:ℝ) ≤ (a-b)^2 := sq_nonneg _
  have h1 := Pab_form3' a b ((a-b)^2) (a*b) rfl rfl
  have h2 := Pab_form2' a b ((a+b)^2) (a*b) rfl rfl
  by_cases hc : 0 ≤ (a*b)^2 - 4*(a*b) + 1
  · have hT : (0:ℝ) ≤ ((a*b)+1)^2 := sq_nonneg _
    have hsq : (0:ℝ) ≤ (3*((a+b)^2) - (14*(a*b)^2 + 4*(a*b) + 14)/6)^2 := sq_nonneg _
    nlinarith [h2, hT, hc, hsq]
  · push Not at hc
    have hT : 0 < a*b := by nlinarith [hc, sq_nonneg (a*b)]
    have h7 : 7*(a*b)^2 - 34*(a*b) + 7 ≤ 0 := by nlinarith [hc, hT, sq_nonneg (a*b)]
    have hs1 : (0:ℝ) ≤ ((a*b)-3)^2 := sq_nonneg _
    have hs2 : (0:ℝ) ≤ (3*(a*b)-1)^2 := sq_nonneg _
    have hcy : 0 ≤ -2*(7*(a*b)^2 - 34*(a*b) + 7)*((a-b)^2) := by nlinarith [h7, hY]
    nlinarith [h1, hs1, hs2, hcy, hY, sq_nonneg (a-b)]

set_option maxHeartbeats 1000000 in
/-- Strict positivity of the orientation polynomial off the excluded half-angle values. -/
theorem Pab_pos (a b : ℝ) (h3 : a^2 ≠ 3) (h1 : 3*a^2 ≠ 1) : 0 < Pab a b := by
  set T := a*b with hTdef
  set X := (a+b)^2 with hXdef
  set Y := (a-b)^2 with hYdef
  have hY0 : 0 ≤ Y := by simp only [hYdef]; positivity
  have hXY : X = 4*T + Y := by simp only [hXdef, hYdef, hTdef]; ring
  have he2 := Pab_form2' a b X T hXdef hTdef
  have he3 := Pab_form3' a b Y T hYdef hTdef
  rcases lt_or_eq_of_le (Pab_nonneg a b) with hlt | heq
  · exact hlt
  · exfalso
    by_cases hc : 0 ≤ T^2 - 4*T + 1
    · have hterm : 0 ≤ (32/9*(T+1)^2)*(T^2 - 4*T + 1) := by
        have h1' : (0:ℝ) ≤ (T+1)^2 := sq_nonneg _
        nlinarith
      have hsq : (3*X - (14*T^2 + 4*T + 14)/6)^2 = 0 := by nlinarith [he2, heq, hterm]
      by_cases hT1 : T + 1 = 0
      · have hTv : T = -1 := by linarith
        have hXv : X = 4/3 := by nlinarith [hsq, hTv]
        have hs1 : a^2 + b^2 = X - 2*T := by simp only [hXdef, hTdef]; ring
        have hs2 : (a^2)*(b^2) = T^2 := by simp only [hTdef]; ring
        have hz : (a^2 - 3)*(3*(a^2) - 1) = 0 := by nlinarith [hs1, hs2, hXv, hTv]
        rcases mul_eq_zero.mp hz with hz | hz
        · exact h3 (by linarith)
        · exact h1 (by linarith)
      · have hprod : (32/9*(T+1)^2)*(T^2 - 4*T + 1) = 0 := by
          nlinarith [he2, heq, hsq, hterm]
        have hT2 : T^2 - 4*T + 1 = 0 := by
          rcases mul_eq_zero.mp hprod with h | h
          · have : (T+1)^2 = 0 := by linarith
            exact absurd ((pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp this) hT1
          · exact h
        have hcval : 14*T^2 + 4*T + 14 = 60*T := by nlinarith [hT2]
        have hXval : X = 10*T/3 := by nlinarith [hsq, hcval]
        have hTle : T ≤ 0 := by nlinarith [hXY, hY0, hXval]
        nlinarith [hT2, hTle, sq_nonneg T]
    · push Not at hc
      have hTpos : 0 < T := by nlinarith [hc, sq_nonneg T]
      have hcoef : 0 ≤ -2*(7*T^2 - 34*T + 7) := by nlinarith [hc, hTpos, sq_nonneg T]
      have hcy : 0 ≤ -2*(7*T^2 - 34*T + 7)*Y := by nlinarith [hcoef, hY0]
      have hkey : (T-3)^2*(3*T-1)^2 = 0 := by nlinarith [he3, heq, hcy, hY0, sq_nonneg Y]
      have hYz : Y = 0 := by nlinarith [he3, heq, hcy, hY0, hkey, sq_nonneg Y]
      have hab : a = b := by
        have h0 : (a - b)^2 = 0 := by rw [← hYdef]; exact hYz
        have h0' : a - b = 0 := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h0
        exact sub_eq_zero.mp h0'
      have hTeq : T = a^2 := by simp only [hTdef, hab]; ring
      rcases mul_eq_zero.mp hkey with hk | hk
      · have hk' : T - 3 = 0 := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp hk
        exact h3 (by rw [← hTeq]; linarith)
      · have hk' : 3*T - 1 = 0 := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp hk
        exact h1 (by rw [← hTeq]; linarith)

/-- The sign of the sum-one area, with the positivity of `Pab` discharged internally. -/
theorem Lamab_pos_iff' (a b : ℝ) (ha : a ≠ 0) (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0) :
    0 < Lamab a b ↔ 0 < a*b*(a+b)*(a*b-1) := by
  have h3 : a^2 ≠ 3 := by intro h; exact h13 (by rw [h]; norm_num)
  have h1 : 3*a^2 ≠ 1 := by intro h; exact h31 (by rw [h]; norm_num)
  exact Lamab_pos_iff a b ha h31 h13 (Pab_pos a b h3 h1)

/-- **Scaling by a nonzero complex number does not change the sign of the oriented area.** -/
lemma im_scale (X A B : ℂ) :
    ((starRingEnd ℂ) (X*A) * (X*B)).im = Complex.normSq X * ((starRingEnd ℂ) A * B).im := by
  have hX : (starRingEnd ℂ) X * X = ((Complex.normSq X : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have h : (starRingEnd ℂ) (X*A) * (X*B) = ((Complex.normSq X : ℝ) : ℂ) * ((starRingEnd ℂ) A * B) := by
    rw [map_mul, ← hX]
    ring
  rw [h, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- **The sum-one area interface.**  If `g - r = X·Ap` and `b - r = X·Bp` with `X ≠ 0` (which
holds for a nondegenerate triangle, `X = toComplex (B-C)`), then the oriented area of the
tricolor triangle is positive exactly when `a·b·(a+b)(ab-1) > 0`. -/
theorem area_of_sum_one (X : ℂ) (hX : X ≠ 0) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hm : mm a b ≠ 0) (h31 : 3*a^2-1 ≠ 0) (h13 : a^2-3 ≠ 0) :
    0 < ((starRingEnd ℂ) (X * Ap a b) * (X * Bp a b)).im ↔ 0 < a*b*(a+b)*(a*b-1) := by
  have hns : 0 < Complex.normSq X := by
    rcases lt_or_eq_of_le (Complex.normSq_nonneg X) with h | h
    · exact h
    · exact absurd (Complex.normSq_eq_zero.mp h.symm) hX
  rw [im_scale, im_key a b ha hb hm h31 h13, mul_pos_iff_of_pos_left hns,
    Lamab_pos_iff' a b ha h31 h13]


/-- **§6, `σ = +1` case** (`u+v+w = 0`, the `001` labels with `N = 1`): the area is positive
exactly when `sin u · sin v · sin w > 0`. -/
theorem Lamab_pos_of_sum_zero (u v w : ℝ) (hu : Real.cos (u/2) ≠ 0) (hv : Real.cos (v/2) ≠ 0)
    (ha : Real.tan (u/2) ≠ 0) (h31 : 3*(Real.tan (u/2))^2 - 1 ≠ 0)
    (h13 : (Real.tan (u/2))^2 - 3 ≠ 0) (hsum : u + v + w = 0) :
    0 < Lamab (Real.tan (u/2)) (Real.tan (v/2)) ↔ 0 < Real.sin u * Real.sin v * Real.sin w := by
  have h3 : (Real.tan (u/2))^2 ≠ 3 := by intro h; exact h13 (by linarith)
  have h1 : 3*(Real.tan (u/2))^2 ≠ 1 := by intro h; exact h31 (by linarith)
  rw [Lamab_pos_iff_sin u v hu hv ha h31 h13 (Pab_pos _ _ h3 h1)]
  have hs : Real.sin (u+v) = -Real.sin w := by
    rw [show u + v = -w by linarith, Real.sin_neg]
  rw [hs, show -(Real.sin u * Real.sin v * (-Real.sin w))
      = Real.sin u * Real.sin v * Real.sin w by ring]

/-- **§6, `σ = -1` case** (`u+v+w = -π`, the `022` and `112` labels with `N = 4`): the area is
positive exactly when `-(sin u · sin v · sin w) > 0`. -/
theorem Lamab_pos_of_sum_neg_pi (u v w : ℝ) (hu : Real.cos (u/2) ≠ 0)
    (hv : Real.cos (v/2) ≠ 0) (ha : Real.tan (u/2) ≠ 0)
    (h31 : 3*(Real.tan (u/2))^2 - 1 ≠ 0) (h13 : (Real.tan (u/2))^2 - 3 ≠ 0)
    (hsum : u + v + w = -Real.pi) :
    0 < Lamab (Real.tan (u/2)) (Real.tan (v/2)) ↔
      0 < -(Real.sin u * Real.sin v * Real.sin w) := by
  have h3 : (Real.tan (u/2))^2 ≠ 3 := by intro h; exact h13 (by linarith)
  have h1 : 3*(Real.tan (u/2))^2 ≠ 1 := by intro h; exact h31 (by linarith)
  rw [Lamab_pos_iff_sin u v hu hv ha h31 h13 (Pab_pos _ _ h3 h1)]
  have hs : Real.sin (u+v) = Real.sin w := by
    rw [show u + v = -(Real.pi + w) by linarith, Real.sin_neg, add_comm (Real.pi) w,
      Real.sin_add_pi]
    ring
  rw [hs]



/-! ### §2 of the derivation: the three vertex coefficients and `λ` in half-angle form

With `ξ = Usq a/Usqc a = e^{2iu}`, `η = Usq b/Usqc b = e^{2iv}` and `ζ = 1/(ξη) = e^{2iw}`
(the sum-one case `u+v+w ∈ πℤ`), the geometric coefficients of `m1_red_nf`, `m1_green_nf`,
`m1_blue_nf` are `c₁ = (1-η)/(1-1/ξ)`, `c₂ = (1-ζ)/(1-1/η)`, `c₃ = (1-ξ)/(1-1/ζ)`, and the
side ratio of `m4d_p_rel` is `λ = ξ³(η³-1)/(ξ³-1)`.  The four theorems below identify these
with `Z1`, `Z2`, `Z3`, `Zl`. -/

lemma Usq_sub_Usqc (a : ℝ) : Usq a - Usqc a = 4*(a:ℂ)*Complex.I := by
  simp only [Usq, Usqc]; push_cast; ring

lemma Usq_prod_sub (a b : ℝ) :
    Usq a * Usq b - Usqc a * Usqc b
      = ((-4:ℝ):ℂ)*Complex.I*(((a:ℂ))+(b:ℂ))*(((a:ℂ)*(b:ℂ))-1) := by
  apply Complex.ext
  · simp only [Usq, Usqc, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
    push_cast
    ring
  · simp only [Usq, Usqc, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
    push_cast
    ring

lemma U6_sub_U6c (a : ℝ) :
    U6 a - U6c a = 4*(a:ℂ)*(((3*a^2-1:ℝ)):ℂ)*(((a^2-3:ℝ)):ℂ)*Complex.I := by
  simp only [U6, U6c]; push_cast; ring

lemma one_sub_div_Usq (a : ℝ) : (1:ℂ) - Usq a/Usqc a = -(4*(a:ℂ)*Complex.I)/Usqc a := by
  have h : Usqc a ≠ 0 := Usqc_ne a
  field_simp
  linear_combination -Usq_sub_Usqc a

lemma one_sub_inv_div_Usq (a : ℝ) :
    (1:ℂ) - 1/(Usq a/Usqc a) = (Usq a - Usqc a)/Usq a := by
  have h : Usq a ≠ 0 := Usq_ne a
  have h2 : Usqc a ≠ 0 := Usqc_ne a
  field_simp

lemma one_sub_inv_prod (a b : ℝ) :
    (1:ℂ) - 1/((Usq a/Usqc a)*(Usq b/Usqc b))
      = (Usq a * Usq b - Usqc a * Usqc b)/(Usq a * Usq b) := by
  have h1 : Usq a ≠ 0 := Usq_ne a
  have h2 : Usqc a ≠ 0 := Usqc_ne a
  have h3 : Usq b ≠ 0 := Usq_ne b
  have h4 : Usqc b ≠ 0 := Usqc_ne b
  field_simp

lemma one_sub_prod (a b : ℝ) :
    (1:ℂ) - 1/(1/((Usq a/Usqc a)*(Usq b/Usqc b)))
      = (Usqc a * Usqc b - Usq a * Usq b)/(Usqc a * Usqc b) := by
  have h1 : Usq a ≠ 0 := Usq_ne a
  have h2 : Usqc a ≠ 0 := Usqc_ne a
  have h3 : Usq b ≠ 0 := Usq_ne b
  have h4 : Usqc b ≠ 0 := Usqc_ne b
  rw [one_div_one_div]
  field_simp

lemma U6_div_sub_one (a : ℝ) (h : U6c a ≠ 0) :
    U6 a / U6c a - 1 = (U6 a - U6c a)/U6c a := by
  field_simp

/-- **§2, first coefficient**: `c₁ = (1-η)/(1-1/ξ) = Z1 a b`. -/
lemma c1_half (a b : ℝ) (ha : a ≠ 0) :
    (1 - Usq b / Usqc b) / (1 - 1/(Usq a / Usqc a)) = Z1 a b := by
  have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have hsa : Usq a ≠ 0 := Usq_ne a
  have hsca : Usqc a ≠ 0 := Usqc_ne a
  have hscb : Usqc b ≠ 0 := Usqc_ne b
  have hne : (1:ℂ) - 1/(Usq a/Usqc a) ≠ 0 := by
    rw [one_sub_inv_div_Usq, Usq_sub_Usqc]
    exact div_ne_zero (by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact ha'
      · exact Complex.I_ne_zero) hsa
  rw [one_sub_inv_div_Usq, Usq_sub_Usqc, one_sub_div_Usq, Z1]
  field_simp

/-- **§2, second coefficient**: `c₂ = (1-ζ)/(1-1/η) = Z2 a b`. -/
lemma c2_half (a b : ℝ) (hb : b ≠ 0) :
    (1 - 1/((Usq a / Usqc a) * (Usq b / Usqc b))) / (1 - 1/(Usq b / Usqc b))
      = Z2 a b := by
  have hb' : (b:ℂ) ≠ 0 := by exact_mod_cast hb
  have hsa : Usq a ≠ 0 := Usq_ne a
  have hsca : Usqc a ≠ 0 := Usqc_ne a
  have hsb : Usq b ≠ 0 := Usq_ne b
  have hscb : Usqc b ≠ 0 := Usqc_ne b
  have hne : (1:ℂ) - 1/(Usq b/Usqc b) ≠ 0 := by
    rw [one_sub_inv_div_Usq, Usq_sub_Usqc]
    exact div_ne_zero (by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact hb'
      · exact Complex.I_ne_zero) hsb
  rw [one_sub_inv_prod, Usq_prod_sub, one_sub_inv_div_Usq, Usq_sub_Usqc, Z2]
  field_simp
  push_cast
  ring

/-- **§2, third coefficient**: `c₃ = (1-ξ)/(1-1/ζ) = Z3 a b`. -/
lemma c3_half (a b : ℝ) (ha : a ≠ 0) (hm : mm a b ≠ 0) :
    (1 - Usq a / Usqc a) / (1 - 1/(1/((Usq a / Usqc a) * (Usq b / Usqc b))))
      = Z3 a b := by
  have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have hsa : Usq a ≠ 0 := Usq_ne a
  have hsca : Usqc a ≠ 0 := Usqc_ne a
  have hsb : Usq b ≠ 0 := Usq_ne b
  have hscb : Usqc b ≠ 0 := Usqc_ne b
  have hab : ((a:ℂ)+(b:ℂ)) ≠ 0 := by
    intro h
    apply hm
    have h' : ((a+b : ℝ) : ℂ) = 0 := by push_cast; exact h
    have h2 : a + b = 0 := by exact_mod_cast h'
    simp only [mm, h2, zero_mul]
  have hab1 : ((a:ℂ)*(b:ℂ)-1) ≠ 0 := by
    intro h
    apply hm
    have h' : ((a*b-1 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have h2 : a*b - 1 = 0 := by exact_mod_cast h'
    simp only [mm, h2, mul_zero]
  have hne : (1:ℂ) - 1/(1/((Usq a / Usqc a) * (Usq b / Usqc b))) ≠ 0 := by
    rw [one_sub_prod,
      show Usqc a * Usqc b - Usq a * Usq b = -(Usq a * Usq b - Usqc a * Usqc b) from by ring,
      Usq_prod_sub]
    apply div_ne_zero
    · apply neg_ne_zero.mpr
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · norm_num
          · exact Complex.I_ne_zero
        · exact hab
      · exact hab1
    · exact mul_ne_zero hsca hscb
  rw [one_sub_div_Usq, one_sub_prod,
    show Usqc a * Usqc b - Usq a * Usq b = -(Usq a * Usq b - Usqc a * Usqc b) from by ring,
    Usq_prod_sub, Z3]
  field_simp
  push_cast
  ring

/-- **§2, the side ratio**: `λ = ξ³(η³-1)/(ξ³-1) = Zl a b`, with `ξ³ = U6 a/U6c a`. -/
lemma lam_half (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h31 : 3*a^2-1 ≠ 0)
    (h13 : a^2-3 ≠ 0) (h31b : 3*b^2-1 ≠ 0) (h13b : b^2-3 ≠ 0) :
    (U6 a / U6c a) * ((U6 b / U6c b) - 1) / ((U6 a / U6c a) - 1) = Zl a b := by
  have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b:ℂ) ≠ 0 := by exact_mod_cast hb
  have h31' : (((3*a^2-1:ℝ)):ℂ) ≠ 0 := by exact_mod_cast h31
  have h13' : (((a^2-3:ℝ)):ℂ) ≠ 0 := by exact_mod_cast h13
  have h31b' : (((3*b^2-1:ℝ)):ℂ) ≠ 0 := by exact_mod_cast h31b
  have h13b' : (((b^2-3:ℝ)):ℂ) ≠ 0 := by exact_mod_cast h13b
  have hU6ca : U6c a ≠ 0 := U6c_ne a
  have hU6cb : U6c b ≠ 0 := U6c_ne b
  have hne : U6 a / U6c a - 1 ≠ 0 := by
    rw [U6_div_sub_one a hU6ca, U6_sub_U6c]
    exact div_ne_zero (by
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · norm_num
            · exact ha'
          · exact h31'
        · exact h13'
      · exact Complex.I_ne_zero) hU6ca
  rw [U6_div_sub_one a hU6ca, U6_sub_U6c, U6_div_sub_one b hU6cb, U6_sub_U6c, Zl]
  field_simp

/-! ### Axiom audit -/

#print axioms M8K.key_identity
#print axioms M8K.im_key
#print axioms M8K.prodW
#print axioms M8K.YDn
#print axioms M8K.im_NN
#print axioms M8K.Pab_pos
#print axioms M8K.Pab_nonneg
#print axioms M8K.Lamab_pos_iff
#print axioms M8K.Lamab_pos_iff'
#print axioms M8K.im_scale
#print axioms M8K.area_of_sum_one
#print axioms M8K.tan_half_mul
#print axioms M8K.tan_sum_prod
#print axioms M8K.Lamab_pos_iff_sin
#print axioms M8K.Lamab_pos_of_sum_zero
#print axioms M8K.Lamab_pos_of_sum_neg_pi
#print axioms M8K.ApW_nf
#print axioms M8K.BpW_nf
#print axioms M8K.ApWc_nf
#print axioms M8K.ZlDn
#print axioms M8K.ZlcDn
#print axioms M8K.ZlZlcDn
#print axioms M8K.c1_half
#print axioms M8K.c2_half
#print axioms M8K.c3_half
#print axioms M8K.lam_half
#print axioms M8K.Usq_prod_sub
#print axioms M8K.U6_sub_U6c

end M8K
