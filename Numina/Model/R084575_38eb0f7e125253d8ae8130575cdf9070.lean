import Mathlib

theorem algebra_165499 (x : ℝ) : (x^2 - 6 * x)^2 - 2 * (x - 3)^2 = 81 ↔
    x = 3 ∨ x = 3 + 2 * Real.sqrt 5 ∨ x = 3 - 2 * Real.sqrt 5 := by
  constructor
  · -- Assume left side: $(x^2 - 6x)^2 - 2(x - 3)^2 = 81$, prove right side.
    intro h
    have h1 : (x^2 - 6 * x)^2 - 2 * (x - 3)^2 = 81 := h
    have h2 : (x - 3) ^ 2 * ((x - 3) ^ 2 - 20) = 0 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x^2 - 6 * x), sq_nonneg (Real.sqrt 5), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · 
      have h5 : (x - 3) ^ 2 = 0 := by linarith
      have h6 : x - 3 = 0 := by
        simp at h5 ⊢
        linarith
      left
      linarith
    · 
      have h5 : (x - 3) ^ 2 = 20 := by linarith
      have h6 : (x - 3) ^ 2 - (2 * Real.sqrt 5) ^ 2 = 0 := by
        have h7 : (2 * Real.sqrt 5) ^ 2 = 20 := by
          calc
            (2 * Real.sqrt 5) ^ 2 = 4 * (Real.sqrt 5) ^ 2 := by ring
            _ = 4 * 5 := by rw [Real.sq_sqrt (by norm_num)]
            _ = 20 := by norm_num
        rw [h5]
        nlinarith
      have h7 : (x - 3 - 2 * Real.sqrt 5) * (x - 3 + 2 * Real.sqrt 5) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · 
        right
        left
        linarith
      · 
        right
        right
        linarith
  · -- Assume right side, prove left side.
    rintro (h | h | h)
    · 
      rw [h]
      norm_num
    · 
      rw [h]
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x^2 - 6 * x), sq_nonneg (Real.sqrt 5), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    · 
      rw [h]
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x^2 - 6 * x), sq_nonneg (Real.sqrt 5), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]