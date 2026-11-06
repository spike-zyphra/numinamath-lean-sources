import Mathlib

theorem algebra_10475 {x y : ℤ} (h : y = 3 * x - 7) (h' : x ≠ 0) (h'' : y ≠ 0)
    (h''' : (x / y : ℚ) = 2 / 5) : x = 14 := by
  have h1 : (x : ℚ) / (y : ℚ) = (2 : ℚ) / (5 : ℚ) := by
    simpa using h'''
  have h2 : (5 * (x : ℚ) = 2 * (y : ℚ)) := by 
    have h3 : (y : ℚ) ≠ 0 := by 
      exact_mod_cast h''
    field_simp [h3] at h1
    linarith
  have h3 : 5 * (x : ℤ) = 2 * (y : ℤ) := by 
    exact_mod_cast h2
  rw [show y = 3 * x - 7 from h] at h3
  linarith