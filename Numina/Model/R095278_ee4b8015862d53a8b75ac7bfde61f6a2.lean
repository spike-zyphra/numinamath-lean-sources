import Mathlib

/- If $x+\frac{1}{y}=y+\frac{1}{z}=1$, find the value of $xyz$.

 -/
theorem algebra_5804 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (h1 : x + 1 / y = 1) (h2 : y + 1 / z = 1) :
    x * y * z = -1 := by
  have eq1 : x * y + 1 = y := by
    field_simp [hy] at h1 
    linarith
  
  have eq2 : y * z + 1 = z := by 
    field_simp [hz] at h2
    linarith

  have h3 : x * y = y - 1 := by linarith
  have h4 : y * z = z - 1 := by linarith
  
  calc 
    x * y * z = (x * y) * z := by ring
    _ = (y - 1) * z := by rw [h3]
    _ = (y * z) - z := by ring
    _ = (z - 1) - z := by rw [h4]
    _ = -1 := by ring