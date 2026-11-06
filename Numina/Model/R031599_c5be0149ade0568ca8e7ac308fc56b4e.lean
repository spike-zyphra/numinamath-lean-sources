import Mathlib

theorem algebra_6000 (f : ℝ → ℝ) :
  ¬ (∀ x y, f (x + y) + f (x - y) - 2 * f x * f (y + 1) = 2 * x * y * (3 * y - x ^ 2)) := by
  intro h
  have h1 := h 0 0
  have h2 := h 1 0
  have h3 := h 0 1
  have h4 := h 1 1
  have h5 := h 2 1
  have h6 := h 1 2
  have h7 := h 0 2
  have h8 := h 2 2
  have h9 := h 3 1
  have h10 := h 1 3
  have h11 := h 2 3
  have h12 := h 3 2
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have h13 : f 1 = 1 := by 
    by_cases h11 : f 1 = 0
    · -- Case f 1 = 0
      rw [h11] at h2 h4
      nlinarith 
    · -- Case f 1 ≠ 0
      have h14 : f 1 = 1 := by
        have h15 : f 1 * (1 - f 1) = 0 := by linarith 
        cases' (mul_eq_zero.mp h15) with h17 h18
        · -- Case f 1 = 0
          exfalso 
          tauto 
        · -- Case 1 - f 1 = 0
          linarith 
      linarith 
  rw [h13] at h4
  nlinarith [sq_nonneg (f 0 - 3), sq_nonneg (f 2 + 1), sq_nonneg (f 1 - 1), sq_nonneg (f (-1)), sq_nonneg (f 3 + 5), sq_nonneg (f 4 - 16)]