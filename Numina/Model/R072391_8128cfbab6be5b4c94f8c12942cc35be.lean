import Mathlib

theorem algebra_6566 {x : ℝ} (hx1 : x > 0) (hx2 : x + 1/x = 5) :
    x^4 + 1/x^4 = 527 := by 
  have h3 : x ≠ 0 := by linarith 
  have h4 : x^2 + 1 / x^2 = (x + 1 / x) ^ 2 - 2 := by
    field_simp [h3]
    <;> ring
  have h1 : x^2 + 1 / x^2 = 23 := by 
    rw [h4, hx2]
    norm_num 
  have h5 : x^4 + 1 / x^4 = (x^2 + 1 / x^2) ^ 2 - 2 := by 
    have h6 : x ≠ 0 := by linarith 
    field_simp [h6]
    <;> ring 
  rw [h5, h1]
  all_goals norm_num