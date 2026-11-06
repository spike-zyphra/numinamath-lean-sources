import Mathlib

theorem algebra_187147 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : 2 / x + y / 3 = 3) (h2 : x / 2 + 3 / y = 3 / 2) :
    (x, y) = (1, 3) ∨ (x, y) = (2, 6) := by
  have eq1 : 2 * 3 + x * y = 9 * x := by
    field_simp [hx] at h1
    linarith

  have eq2 : x * y + 6 = 3 * y := by
    field_simp [hy] at h2
    linarith
  
  have eq3 : x * y = 9 * x - 6 := by 
    linarith

  have eq4 : x * y = 3 * y - 6 := by
    linarith

  have eq5 : 9 * x = 3 * y := by
    linarith [eq3, eq4]

  have eq6 : y = 3 * x := by 
    nlinarith
  
  rw [eq6] at eq3
  
  have h3 : 3 * x^2 - 9 * x + 6 = 0 := by 
    nlinarith
  
  have h4 : (x - 1) * (x - 2) = 0 := by 
    nlinarith
  
  cases' (mul_eq_zero.mp h4) with h5 h6

  · -- Case h5: x - 1 = 0, so x = 1
    have hx1 : x = 1 := by 
      linarith
    have hy1 : y = 3 := by 
      rw [hx1] at eq6
      linarith
    left
    simp [hx1, hy1]

  · -- Case h6: x - 2 = 0, so x = 2
    have hx2 : x = 2 := by 
      linarith
    have hy2 : y = 6 := by 
      rw [hx2] at eq6
      linarith
    right
    simp [hx2, hy2]