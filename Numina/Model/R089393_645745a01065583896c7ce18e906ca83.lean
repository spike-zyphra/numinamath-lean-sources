import Mathlib

theorem algebra_180059 (x : ℝ) : (1 + x)^4 = 16 * x^2 ↔ x = 1 ∨ x = -3 + Real.sqrt 8 ∨ x = -3 - Real.sqrt 8 := by 
  constructor
  · -- Forward direction: if (1+x)^4 = 16*x^2, then x is 1 or -3 ± sqrt(8)
    intro h
    have h1 : (1 + x)^4 - 16 * x^2 = 0 := by linarith
    have h2 : (1 + x)^4 - 16 * x^2 = (x - 1)^2 * (x^2 + 6 * x + 1) := by
      ring
    rw [h2] at h1
    cases' (mul_eq_zero.mp h1) with h3 h4
    · -- Case where (x - 1)^2 = 0
      have h5 : x - 1 = 0 := by
        apply pow_eq_zero 
        exact h3
      have hx : x = 1 := by linarith
      left
      exact hx
    · -- Case where x^2 + 6 x + 1 = 0
      have h6 : x^2 + 6 * x + 1 = 0 := by linarith
      have h7 : (x + 3)^2 = 8 := by
        nlinarith
      have h8 : x + 3 = Real.sqrt 8 ∨ x + 3 = -Real.sqrt 8 := by 
        have h9 : (x + 3)^2 = 8 := h7
        have h10 : x + 3 = Real.sqrt 8 ∨ x + 3 = -Real.sqrt 8 := by
          apply eq_or_eq_neg_of_sq_eq_sq
          norm_num
          all_goals nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (8:ℝ) ≥ 0 by norm_num)]
        exact h10
      cases' h8 with h9 h10
      · -- Case where x + 3 = Real.sqrt 8
        have hx : x = -3 + Real.sqrt 8 := by linarith
        right
        left
        exact hx
      · -- Case where x + 3 = -Real.sqrt 8
        have hx : x = -3 - Real.sqrt 8 := by linarith
        right
        right
        exact hx
  · -- Backward direction: if x is 1 or -3 ± sqrt(8), then (1+x)^4 = 16*x^2
    rintro (h | h | h)
    · -- Case x = 1
      rw [h]
      norm_num
    · -- Case x = -3 + Real.sqrt 8
      rw [h]
      have h2 : Real.sqrt 8 ≥ 0 := by positivity
      nlinarith [Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num), pow_two_nonneg (Real.sqrt 8 - 2), pow_two_nonneg (Real.sqrt 8 + 2)]
    · -- Case x = -3 - Real.sqrt 8
      rw [h]
      have h2 : Real.sqrt 8 ≥ 0 := by positivity
      nlinarith [Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num), pow_two_nonneg (Real.sqrt 8 - 2), pow_two_nonneg (Real.sqrt 8 + 2)]