import Mathlib

theorem algebra_227 (x : ℝ) (hx : 2 - x ^ 2 ≥ 0 ∧ x ^ 2 + 8 ≥ 0) : Real.sqrt (2 - x ^ 2) + Real.sqrt (x ^ 2 + 8) = 4 ↔ x = 1 ∨ x = -1 := by
  constructor
  · -- Assume the equation holds, prove x = 1 or x = -1
    intro h
    have ha1 : Real.sqrt (2 - x ^ 2) ≥ 0 := by positivity
    have hb1 : Real.sqrt (x ^ 2 + 8) ≥ 0 := by positivity
    have h1 : Real.sqrt (2 - x ^ 2) = 4 - Real.sqrt (x ^ 2 + 8) := by linarith
    have h2 : (Real.sqrt (2 - x ^ 2)) ^ 2 = (4 - Real.sqrt (x ^ 2 + 8)) ^ 2 := by
      rw [h1]
    have h3 : (Real.sqrt (2 - x ^ 2)) ^ 2 = 2 - x ^ 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h4 : (4 - Real.sqrt (x ^ 2 + 8)) ^ 2 = 16 - 8 * Real.sqrt (x ^ 2 + 8) + (Real.sqrt (x ^ 2 + 8)) ^ 2 := by
      ring
    have h5 : (Real.sqrt (x ^ 2 + 8)) ^ 2 = x ^ 2 + 8 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h3, h4, h5] at h2
    -- Now we have 2 - x^2 = 16 - 8 * sqrt(x^2 + 8) + (x^2 + 8)
    -- which simplifies to 8 * sqrt(x^2 + 8) = 22 + 2x^2
    have h6 : 8 * Real.sqrt (x ^ 2 + 8) = 22 + 2 * x ^ 2 := by
      nlinarith
    have h7 : Real.sqrt (x ^ 2 + 8) = (22 + 2 * x ^ 2) / 8 := by
      linarith
    have h8 : (Real.sqrt (x ^ 2 + 8)) ^ 2 = ((22 + 2 * x ^ 2) / 8) ^ 2 := by
      rw [h7]
    rw [h5] at h8
    -- Now we have x^2 + 8 = ((22 + 2x^2) / 8)^2
    -- which leads to the polynomial equation
    have h9 : (x ^ 2 + 8) = ((22 + 2 * x ^ 2) / 8) ^ 2 := by
      linarith
    -- Now multiply both sides by 64 to clear the denominator
    have h10 : x ^ 4 + 6 * x ^ 2 - 7 = 0 := by
      nlinarith [h9]
    -- Factor the polynomial
    have h11 : (x ^ 2 + 7) * (x ^ 2 - 1) = 0 := by
      nlinarith [h10]
    cases' (mul_eq_zero.1 h11) with h12 h13
    · -- Case where x^2 + 7 = 0, which is impossible
      nlinarith [sq_nonneg x]
    · -- Case where x^2 - 1 = 0, so x^2 = 1
      have h14 : x ^ 2 = 1 := by
        linarith
      have h15 : x = 1 ∨ x = -1 := by
        have h : x ^ 2 = 1 := h14
        have : x = 1 ∨ x = -1 := by
          rw [sq_eq_one_iff] at h
          exact h
        assumption
      exact h15
  · -- Assume x = 1 or x = -1, prove the equation holds
    rintro (h | h)
    · -- Case x = 1
      rw [h]
      have h1 : Real.sqrt (2 - (1 : ℝ) ^ 2) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt ((1 : ℝ) ^ 2 + 8) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      all_goals norm_num
    · -- Case x = -1
      rw [h]
      have h3 : Real.sqrt (2 - (-1 : ℝ) ^ 2) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h4 : Real.sqrt ((-1 : ℝ) ^ 2 + 8) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h3, h4]
      all_goals norm_num