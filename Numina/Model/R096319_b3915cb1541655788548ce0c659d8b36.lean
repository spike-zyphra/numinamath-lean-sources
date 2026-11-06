import Mathlib

theorem algebra_4268 {n : ℤ} (hn : n > 0) (h : (200 * 2546 + n * 201) / 201 = 2546) :
    n ≤ 27 := by 
  omega -- This solves the integer arithmetic goal directly