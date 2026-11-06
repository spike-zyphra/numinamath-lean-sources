import Mathlib

theorem algebra_21132 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (h₀ : x + y + z = 6) (h₁ : 1 / x + 1 / y + 1 / z = 2) : (x + y) / z + (y + z) / x + (x + z) / y = 9 := by
  have h2 : x + y = 6 - z := by linarith
  have h3 : y + z = 6 - x := by linarith
  have h4 : x + z = 6 - y := by linarith
  have h5 : (x + y) / z = (6 / z) - 1 := by
    rw [h2]
    field_simp [hz]
    <;> ring
  have h6 : (y + z) / x = (6 / x) - 1 := by
    rw [h3]
    field_simp [hx]
    <;> ring
  have h7 : (x + z) / y = (6 / y) - 1 := by
    rw [h4]
    field_simp [hy]
    <;> ring
  calc 
    (x + y) / z + (y + z) / x + (x + z) / y
        = ((6 / z) - 1) + ((6 / x) - 1) + ((6 / y) - 1) := by rw [h5, h6, h7]
    _ = (6 / z + 6 / x + 6 / y) - 3 := by ring
    _ = 6 * (1 / x + 1 / y + 1 / z) - 3 := by 
      field_simp [hx, hy, hz]
      <;> ring
    _ = 6 * 2 - 3 := by rw [h₁]
    _ = (12 - 3 : ℝ) := by norm_num
    _ = (9 : ℝ) := by norm_num