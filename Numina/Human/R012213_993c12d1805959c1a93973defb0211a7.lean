import Mathlib

-- we show vieta's formula
lemma vieta_formula {p q x1 x2: ℝ} (ne: ¬x1 = x2) (h1: x1 ^ 2 + p * x1 + q = 0) (h2: x2 ^ 2 + p * x2 + q = 0):
    x1 + x2 = -p ∧ x1 * x2 = q := by

  have h: (x1 - x2) * (x1 + x2 + p) = 0 := by nlinarith
  replace ne: ¬ x1 - x2 = 0 := by
    by_contra! i
    replace i: x1 = x2 := by linarith
    simp [i] at ne
  simp [ne] at h
  constructor
  .
    linarith
  .
    have f: (x1 + x2) ^ 2 - 2 * (x1 * x2) + p * (x1 + x2) + 2 * q = 0 := by
      nlinarith
    replace h: x1 + x2 = -p := by linarith
    simp [h] at f
    nlinarith

-- we give the condition for a quadratic trinomial to have two distinct real roots
lemma two_distinct_real_roots {p q: ℝ} (h: 0 < p ^ 2 - 4 * q): ∃ x1 x2, x1 ≠ x2 ∧
  x1 ^ 2 + p * x1 + q = 0 ∧ x2 ^ 2 + p * x2 + q = 0 := by
   set r:= p ^ 2 - 4 * q
   let x1:= (-p + √r) / 2
   let x2:= (-p - √r) / 2
   use x1
   use x2
   constructor
   .
    by_contra! o
    simp [x1, x2] at o
    field_simp at o
    replace o: √r = 0 := by linarith
    rw [Real.sqrt_eq_zero] at o
    simp [o] at h
    have eq: √(p ^ 2 - q * 4) ^ 2 = p ^ 2 - q * 4 := by
      symm
      rw [← Real.sqrt_eq_iff_eq_sq]
      simp [r] at h
      linarith
      apply Real.sqrt_nonneg
    linarith
   .
    constructor
    .
      simp [x1]
      field_simp
      ring_nf
      have eq: √(p ^ 2 - q * 4) ^ 2 = p ^ 2 - q * 4 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        simp [r] at h
        linarith
        apply Real.sqrt_nonneg
      rw [eq]
      clear eq
      ring
    .
      simp [x2]
      field_simp
      ring_nf
      have eq: √(p ^ 2 - q * 4) ^ 2 = p ^ 2 - q * 4 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        simp [r] at h
        linarith
        apply Real.sqrt_nonneg
      rw [eq]
      clear eq
      ring

/-The quadratic trinomial
y=x^2+ax+b has real roots
t and l, where −1 < t < 0.
Prove that if t is added to the coefficients a and b,
then the resulting trinomial will also have two distinct real roots.-/

theorem algebra_118790 {a b t l: ℝ} (ne: t ≠ l) (ht: t ^ 2 + a * t + b = 0) (hl: l ^ 2 + a * l + b = 0)
    (l1: -1 < t) (l2: t < 0): ∃ x1 x2, x1 ≠ x2 ∧
  x1 ^ 2 + (a + t) * x1 + (b + t) = 0 ∧ x2 ^ 2 + (a + t) * x2 + (b + t) = 0 := by

   apply two_distinct_real_roots
   have i:= vieta_formula ne ht hl
   rcases i with ⟨i, j⟩
   replace i: a = -t - l := by
     linarith
   rw [i, ← j]
   have eq: (-t - l + t) ^ 2 - 4 * (t * l + t) = (l - 2 * t) ^ 2 - 4 * t * (1 + t) := by ring
   rw [eq]
   clear eq
   nlinarith