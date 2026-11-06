import Mathlib

theorem algebra_185653 {a b c : ℝ} (h : a + b + c = 0) :
    a^3 + b^3 + c^3 = 3 * a * b * c := by 
  have eq2 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = 0 := by
    have eq1 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by 
      ring 
    rw [eq1]
    rw [h]
    norm_num
  linarith [eq2]