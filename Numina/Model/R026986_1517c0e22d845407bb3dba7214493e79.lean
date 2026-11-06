import Mathlib

theorem algebra_172916 (x : ℂ) (hx : x^3 = -27 * .I) :
    x = 3 * Real.sqrt 3 / 2 - 3 / 2 * .I ∨ x = 3 * .I ∨ x = -3 * Real.sqrt 3 / 2 - 3 / 2 * .I := by
  have h1 : x^3 + 27 * Complex.I = 0 := by
    have h2 : x^3 = -27 * Complex.I := hx
    calc
      x^3 + 27 * Complex.I = x^3 - (-27 * Complex.I) := by ring_nf
      _ = 0 := by
        rw [show x^3 = -27 * Complex.I by exact h2]
        ring_nf
  have h2 : (x - (3 * Complex.I)) * (x - (-3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I)) * (x - (3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I)) = 0 := by
    have h4 : (x - (3 * Complex.I)) * (x - (-3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I)) * (x - (3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I)) = x^3 + 27 * Complex.I := by
      simp [pow_two, pow_succ, Complex.ext_iff, Complex.I_mul_I, mul_add, sub_mul, mul_sub, mul_assoc, mul_add, mul_sub, mul_assoc, mul_add, mul_sub, mul_assoc, Real.sqrt_mul_self]
      field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      <;> ring
    rw [h4, h1]
  cases' (mul_eq_zero.mp h2) with h5 h6
  · cases' (mul_eq_zero.mp h5) with h7 h8
    · -- Case where the first factor is zero
      have h8 : x = 3 * Complex.I := by
        have h9 : x - (3 * Complex.I) = 0 := by
          simpa using h7
        have h10 : x = (3 * Complex.I) := by
          calc
            x = (x - (3 * Complex.I)) + (3 * Complex.I) := by ring_nf
            _ = (0) + (3 * Complex.I) := by rw [h9]
            _ = 3 * Complex.I := by ring_nf
        exact h10
      right
      left
      exact h8
    · -- Case where the second factor is zero
      have h9 : x = -3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I := by
        have h10 : x - (-3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I) = 0 := by
          simpa using h8
        have h11 : x = (-3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I) := by
          calc
            x = (x - (-3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I)) + (-3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I) := by ring_nf
            _ = (0) + (-3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I) := by rw [h10]
            _ = -3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I := by ring_nf
        exact h11
      right
      right
      exact h9
  · -- Case where the third factor is zero
    have h10 : x = 3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I := by
      have h11 : x - (3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I) = 0 := by
        simpa using h6
      have h12 : x = (3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I) := by
        calc
          x = (x - (3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I)) + (3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I) := by ring_nf
          _ = (0) + (3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I) := by rw [h11]
          _ = 3 * Real.sqrt 3 / 2 - 3 / 2 * Complex.I := by ring_nf
      exact h12
    left
    exact h10