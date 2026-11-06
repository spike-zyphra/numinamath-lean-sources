import Mathlib

theorem algebra_101723 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (10 * a + b) + (10 * b + a) = 3 * (a + b) * a) :
    10 * a + b = 37 := by
  have eq1 : (10 * a + b) + (10 * b + a) = 11 * (a + b) := by
    ring
  rw [eq1] at h
  have eq2 : 11 * (a + b) = 3 * (a + b) * a := by 
    linarith 
  by_cases h1 : a + b > 0 
  · -- Assume a + b > 0
    have h2 : a ≤ 11 := by 
      nlinarith [sq_pos_of_ne_zero (show (a : ℕ) ≠ 0 by exact ha), sq_pos_of_ne_zero (show (b : ℕ) ≠ 0 by exact hb), sq_nonneg (a : ℤ), sq_nonneg (b : ℤ)]
    interval_cases a <;> omega 
  · -- Assume a + b ≤ 0
    have h2 : a + b = 0 := by 
      omega 
    have h3 : a = 0 := by 
      omega 
    have h4 : b = 0 := by 
      omega 
    contradiction