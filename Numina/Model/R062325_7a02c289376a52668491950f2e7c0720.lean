import Mathlib

theorem algebra_288381 (v1 v2 : ℝ) (h1 : v1 > 0) (h2 : v2 > 0)
    (h3 : v1 * 30 = v2 * 25) :
    (v2 - v1) / v1 * 100 = 20 := by

  have h4 : v2 = (30 / 25) * v1 := by
    linarith
  
  have h5 : v2 - v1 = (1 / 5) * v1 := by
    rw [h4]
    linarith
  
  have h6 : (v2 - v1) / v1 * 100 = 20 := by
    rw [h5]
    field_simp [h1.ne']
    <;> linarith
  
  exact h6