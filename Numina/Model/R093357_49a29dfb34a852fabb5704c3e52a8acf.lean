import Mathlib

theorem algebra_253906 {x y : ℝ} (h : x / y = 2) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x - y) / x = 1 / 2 := by 
  have h1 : x = 2 * y := by
    field_simp [hy] at h 
    linarith 
  have h2 : x - y = y := by
    rw [h1]
    ring 
  have eq1 : (x - y) / x = y / x := by
    rw [h2]
  have h5 : y / x = 1 / 2 := by 
    rw [h1]
    field_simp [hy, show y ≠ 0 by exact hy]
    <;> ring 
  rw [eq1]
  exact h5