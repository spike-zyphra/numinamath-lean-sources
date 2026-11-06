import Mathlib

theorem algebra_163745 (x : ℂ) :
    x^4 - x^2 + 8 * x - 16 = 0 ↔
    x = (-1 / 2) * (1 + Real.sqrt 17) ∨
    x = (-1 / 2) * (1 - Real.sqrt 17) ∨
    x = (1 / 2) * (1 + Real.sqrt 15 * Complex.I) ∨
    x = (1 / 2) * (1 - Real.sqrt 15 * Complex.I) := by
  constructor
  · -- Forward direction: if x^4 - x^2 + 8 * x - 16 = 0 then x is one of the four roots
    intro h
    have h1 : x^4 - x^2 + 8 * x - 16 = (x^2 - x + 4) * (x^2 + x - 4) := by
      ring
    rw [h1] at h
    cases (mul_eq_zero.mp h) with
    | inl h2 =>
      have h3 : x^2 - x + 4 = 0 := h2
      have h4 : x^2 - x + 4 = (x - (1 / 2) * (1 + Real.sqrt 15 * Complex.I)) * (x - (1 / 2) * (1 - Real.sqrt 15 * Complex.I)) := by
        ring_nf
        simp [pow_two, Complex.ext_iff, mul_add, sub_eq_zero, Complex.I_sq]
        ring_nf
        <;> norm_num [Real.sqrt_sq]
        <;> ring
      rw [h4] at h3
      cases (mul_eq_zero.mp h3) with
      | inl h5 =>
        right
        right
        left
        exact eq_of_sub_eq_zero h5
      | inr h6 =>
        right
        right
        right
        exact eq_of_sub_eq_zero h6
    | inr h2 =>
      have h3 : x^2 + x - 4 = 0 := h2
      have h4 : x^2 + x - 4 = (x - (-1 / 2) * (1 + Real.sqrt 17)) * (x - (-1 / 2) * (1 - Real.sqrt 17)) := by
        ring_nf
        simp [pow_two, Complex.ext_iff, mul_add, sub_eq_zero]
        <;> ring_nf
        <;> norm_num [Real.sqrt_sq]
        <;> ring
      rw [h4] at h3
      cases (mul_eq_zero.mp h3) with
      | inl h5 =>
        left
        exact eq_of_sub_eq_zero h5
      | inr h6 =>
        right
        left
        exact eq_of_sub_eq_zero h6
  · -- Reverse direction: the four roots satisfy the equation
    rintro (h | h | h | h)
    · -- First root
      rw [h]
      simp [pow_two, pow_succ, Complex.ext_iff, sub_eq_zero, mul_add, add_mul]
      field_simp
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
    · -- Second root
      rw [h]
      simp [pow_two, pow_succ, Complex.ext_iff, sub_eq_zero, mul_add, add_mul]
      field_simp
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
    · -- Third root
      rw [h]
      simp [pow_two, pow_succ, Complex.ext_iff, sub_eq_zero, mul_add, add_mul]
      field_simp [Complex.I_sq]
      <;> ring_nf <;> norm_num [Real.sqrt_sq]
      <;> ring
    · -- Fourth root
      rw [h]
      simp [pow_two, pow_succ, Complex.ext_iff, sub_eq_zero, mul_add, add_mul]
      field_simp [Complex.I_sq]
      <;> ring_nf <;> norm_num [Real.sqrt_sq]
      <;> ring