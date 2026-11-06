import Mathlib

theorem algebra_153665 (x : ℝ) : Real.sqrt (x^2 - 1) = Real.sqrt 3 ↔ x = 2 ∨ x = -2 := by
  constructor
  · -- Assume Real.sqrt (x ^ 2 - 1) = Real.sqrt 3, prove x = 2 ∨ x = -2
    intro h
    have h1 : x^2 - 1 ≥ 0 := by
      by_contra h1
      push_neg at h1
      have h2 : Real.sqrt (x^2 - 1) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
        all_goals linarith
      have h3 : Real.sqrt 3 > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals linarith
      have h4 : Real.sqrt 3 = 0 := by linarith [h2, h]
      linarith
    have h4 : x^2 - 1 = 3 := by
      have h5 : Real.sqrt (x ^ 2 - 1) = Real.sqrt 3 := h
      have h6 : x^2 - 1 = (Real.sqrt (x ^ 2 - 1)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      have h7 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      rw [h5] at h6
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (x ^ 2 - 1)]
    have h5 : x^2 = 4 := by
      linarith
    have h6 : x = 2 ∨ x = -2 := by
      have h7 : x^2 - 4 = 0 := by
        linarith [h5]
      have h8 : (x - 2) * (x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · left
        linarith
      · right
        linarith
    exact h6
  · -- Assume x = 2 ∨ x = -2, prove Real.sqrt (x^2 - 1) = Real.sqrt 3
    rintro (h | h)
    · -- Case x = 2
      rw [h]
      have h2 : Real.sqrt ((2 : ℝ) ^ 2 - 1) = Real.sqrt 3 := by
        norm_num
      linarith
    · -- Case x = -2
      rw [h]
      have h2 : Real.sqrt ((-2 : ℝ) ^ 2 - 1) = Real.sqrt 3 := by
        norm_num
      linarith