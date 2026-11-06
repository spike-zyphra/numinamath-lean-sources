import Mathlib

theorem algebra_21408 {x y z : ℚ} (h1 : 2 * x = 5 * y) (h2 : 7 * y = 10 * z) (hx : x ≠ 0) :
    z / x = 7 / 25 := by

  have hy : y = 2 / 5 * x := by 
    linarith

  have hz : z = 7 / 25 * x := by 
    rw [hy] at h2
    linarith
  
  have hfrac : z / x = 7 / 25 := by
    rw [hz]
    field_simp [hx]
    <;> linarith
  
  exact hfrac