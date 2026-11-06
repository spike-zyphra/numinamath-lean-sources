import Mathlib
theorem algebra_9276 {f : Polynomial ℤ} {X : ℤ} (hf : f = 5 * X ^ 5 + 4 * X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + X) (h : X = 3) : f = 1641 := by 
  rw [hf, h]
  all_goals norm_num