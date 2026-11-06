import Mathlib

theorem algebra_73 (x : ℝ) (hx : x ≠ 0) (h : 9 / x ^ 2 - 6 / x + 1 = 0) : x / 3 + 3 / x = 2 := by 
  have eq1 : 9 / x ^ 2 - 6 / x + 1 = (3 / x - 1) ^ 2 := by
    field_simp [hx]
    ring 
  rw [eq1] at h 
  have h1 : 3 / x - 1 = 0 := by 
    apply pow_eq_zero 
    exact h 
  have h2 : 3 / x = 1 := by 
    linarith 
  have h3 : x = 3 := by 
    field_simp [hx] at h2 
    linarith 
  rw [h3]
  field_simp 
  <;> norm_num