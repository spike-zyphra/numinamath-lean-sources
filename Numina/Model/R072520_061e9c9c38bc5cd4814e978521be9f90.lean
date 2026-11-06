import Mathlib

theorem calculus_306784 {x y : ℝ} (h1 : x - y - 2 = 0) (h2 : 2 * y^2 + y - 4 = 0) :
    x / y - y = 3 / 2 := by 
  have hx : x = y + 2 := by linarith 
  have hy : y ≠ 0 := by
    by_contra h
    rw [h] at h2 
    nlinarith
  have eq1 : x / y - y = (y + 2 - y^2) / y := by
    rw [hx]
    field_simp [hy]
    <;> ring
  have eq2 : (y + 2 - y^2) / y = 3 / 2 := by
    have h3 : y + 2 - y^2 = 3 * y / 2 := by 
      nlinarith [h2]
    have h4 : (y + 2 - y^2) / y = (3 * y / 2) / y := by 
      rw [h3]
    have h5 : (3 * y / 2) / y = 3 / 2 := by 
      field_simp [hy]
      <;> nlinarith 
    linarith [h4, h5]
  linarith [eq1, eq2]