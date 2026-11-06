import Mathlib

def nabla (m n : ℤ) := ∑ i in Finset.Icc m n, i

theorem algebra_253451 : (nabla 22 26 : ℚ) / nabla 4 6 = 8 := by
  have h1 : (nabla 22 26 : ℚ) = 120 := by 
    native_decide 
  have h2 : (nabla 4 6 : ℚ) = 15 := by
    native_decide
  rw [h1, h2]
  norm_num