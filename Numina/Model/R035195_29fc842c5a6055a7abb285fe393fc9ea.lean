import Mathlib

theorem algebra_34572 {x : ℝ} (h : 3 ≠ x) (h' : (3 ^ 2 - x ^ 2) / (2 * x - 2 * 3) = -10) :
    x = 17 := by
  have hx1 : 2 * x - 2 * 3 ≠ 0 := by
    intro h1
    have h2 : x = 3 := by linarith 
    tauto

  have eq1 : 3 ^ 2 - x ^ 2 = -10 * (2 * x - 2 * 3) := by 
    have eq2 : 2 * x - 2 * 3 ≠ 0 := hx1
    field_simp [eq2] at h'
    linarith 
  have eq2 : x ^ 2 - 20 * x + 51 = 0 := by
    linarith [eq1] 
  have eq3 : (x - 3) * (x - 17) = 0 := by
    nlinarith [eq2]
  cases' (mul_eq_zero.mp eq3) with h4 h5 
  · -- x - 3 = 0 
    have h3 : x = 3 := by linarith 
    tauto 
  · -- x - 17 = 0 
    linarith