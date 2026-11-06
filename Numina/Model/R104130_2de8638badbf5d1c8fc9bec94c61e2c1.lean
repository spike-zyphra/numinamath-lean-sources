import Mathlib

theorem algebra_298818 (x : ℝ) (hx : x^2 + 2 * x - 3 ≠ 0) :
    (7 * x - 8) / (x^2 + 2 * x - 3) = (29 / (4 * (x + 3))) - (1 / (4 * (x - 1))) := by
  have h1 : x^2 + 2 * x - 3 ≠ 0 := hx
  have h2 : (x + 3) * (x - 1) = x^2 + 2 * x - 3 := by ring
  have h3 : x + 3 ≠ 0 := by 
    intro h4
    have : x^2 + 2 * x - 3 = 0 := by
      have h5 : x = -3 := by linarith
      rw [h5]
      norm_num
    contradiction 
  have h4 : x - 1 ≠ 0 := by 
    intro h5
    have : x^2 + 2 * x - 3 = 0 := by 
      have h6 : x = 1 := by linarith
      rw [h6]
      norm_num 
    contradiction
  have eq1 : (7 * x - 8) / (x^2 + 2 * x - 3) = (7 * x - 8) / ((x + 3) * (x - 1)) := by rw [h2]

  rw [eq1]
  field_simp [(show (x + 3) ≠ 0 by assumption), (show (x - 1) ≠ 0 by assumption)]
  <;> ring
  <;> field_simp [(show (x + 3) ≠ 0 by assumption), (show (x - 1) ≠ 0 by assumption)]
  <;> nlinarith