import Mathlib

theorem algebra_20890 (x : ℝ) (hx : 0 ≤ x - 4) : Real.sqrt (x - 4) = 4 ↔ x = 20 := by
  constructor
  · -- Forward direction: Assume √(x - 4) = 4, prove x = 20
    intro h
    have h1 : (Real.sqrt (x - 4)) ^ 2 = (4 : ℝ) ^ 2 := by 
      rw [h]
    have h2 : (Real.sqrt (x - 4)) ^ 2 = x - 4 := by 
      rw [Real.sq_sqrt]
      linarith
    have h3 : (4 : ℝ) ^ 2 = 16 := by norm_num
    linarith [h2, h3, h1]
  · -- Backward direction: Assume x = 20, prove √(x - 4) = 4
    intro h
    rw [h]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    all_goals norm_num