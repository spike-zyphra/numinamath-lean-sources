import Mathlib

theorem algebra_98180 (a b : ℝ) (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 4 - b * x ^ 2 + x + 5)
    (h : f (-3) = 2) : f 3 = 8 := by
  have eq1 : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 := by 
    rw [hf]
  rw [eq1] at h
  have eq2 : 81 * a - 9 * b = 0 := by
    norm_num at h 
    linarith
  
  have eq3 : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := by
    rw [hf]

  have eq4 : b = 9 * a := by
    linarith [eq2]

  rw [eq3]
  rw [eq4]
  norm_num
  <;> linarith