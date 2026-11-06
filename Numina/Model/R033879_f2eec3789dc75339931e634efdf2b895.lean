import Mathlib

theorem number_theory_213816 (x y z : ℤ) (h : x * y + y * z + z * x = 1) :
    IsSquare ((1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2)) := by
  have h1 : (1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2) = (x * y * z - (x + y + z)) ^ 2 := by 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x + y + z - x * y * z), h]
  rw [h1]
  exact ⟨x * y * z - (x + y + z), by ring⟩