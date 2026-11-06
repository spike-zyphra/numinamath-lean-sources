import Mathlib

theorem algebra_1116 (a b S : ℕ) (h : a + b = S)
: (2 * (3 + a)) + (2 * (3 + b)) = 12 + 2 * S := by 
  calc 
    (2 * (3 + a)) + (2 * (3 + b)) = 2 * ( (3 + a) + (3 + b) ) := by
      ring
    _ = 2 * (6 + (a + b)) := by 
      omega
    _ = 2 * (6 + S) := by 
      rw [h]
    _ = 12 + 2 * S := by 
      ring