import Mathlib

theorem algebra_9015 (x : ℂ) :
    x ^ 2 + 2 * x + 3 = 0 ↔ x = -1 + √ 2 * .I ∨ x = -1 - √ 2 * .I := by
  constructor
  · -- Assume x^2 + 2 * x + 3 = 0 prove ∨ statement
    intro h
    have h1 : x ^ 2 + 2 * x + 3 = 0 := h
    have h2 : x ^ 2 + 2 * x + 3 = (x - (-1 + Real.sqrt 2 * Complex.I)) * (x - (-1 - Real.sqrt 2 * Complex.I)) := by
      simp [pow_two, Complex.ext_iff, mul_add, mul_sub, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring_nf
      <;> norm_num [Real.sqrt_sq, pow_two]
      <;> ring
    rw [h2] at h1
    cases (mul_eq_zero.mp h1) with
    | inl h3 =>
      left
      have h4 : x - (-1 + Real.sqrt 2 * Complex.I) = 0 := h3
      have h5 : x = -1 + Real.sqrt 2 * Complex.I := by
        calc
          x = (x - (-1 + Real.sqrt 2 * Complex.I)) + (-1 + Real.sqrt 2 * Complex.I) := by ring_nf
          _ = (-1 + Real.sqrt 2 * Complex.I) := by rw [h4]; all_goals simp
      exact_mod_cast h5
    | inr h4 =>
      right
      have h4' : x - (-1 - Real.sqrt 2 * Complex.I) = 0 := h4
      have h5 : x = -1 - Real.sqrt 2 * Complex.I := by
        calc
          x = (x - (-1 - Real.sqrt 2 * Complex.I)) + (-1 - Real.sqrt 2 * Complex.I) := by ring_nf
          _ = (-1 - Real.sqrt 2 * Complex.I) := by rw [h4']; all_goals simp
      exact_mod_cast h5
  · -- Assume the ∨ statement prove x^2 + 2 * x + 3 = 0
    rintro (h | h)
    · -- Assume x = -1 + √ 2 * .I
      rw [h]
      field_simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, add_mul]
      ring_nf
      <;> norm_num [Real.sqrt_sq]
    · -- Assume x = -1 - √ 2 * .I
      rw [h]
      field_simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, add_mul]
      ring_nf
      <;> norm_num [Real.sqrt_sq]