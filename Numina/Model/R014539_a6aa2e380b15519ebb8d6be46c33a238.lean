import Mathlib

theorem algebra_73039 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x + 1 / y = 10) (h2 : y + 1 / x = 5 / 12) :
    x = 4 ∨ x = 6 := by

  have eq1 : x * y + 1 = 10 * y := by
    field_simp [hy] at h1
    linarith

  have eq2 : x * y + 1 = (5 / 12) * x := by
    field_simp [hx] at h2
    linarith

  have eq3 : 10 * y = (5 / 12) * x := by
    linarith [eq1, eq2]

  have eq4 : x = 24 * y := by
    linarith

  rw [eq4] at eq1
  have eq5 : 24 * y ^ 2 - 10 * y + 1 = 0 := by
    nlinarith
  
  have h3 : (y - 1 / 4) * (y - 1 / 6) = 0 := by 
    nlinarith
  
  cases' (mul_eq_zero.1 h3) with hy1 hy2

  · -- y = 1/4 
    have hy1' : y = 1 / 4 := by 
      linarith

    have hx1 : x = 6 := by
      nlinarith [eq4, hy1']
    
    right
    linarith

  · -- y = 1/6 
    have hy2' : y = 1 / 6 := by 
      linarith

    have hx2 : x = 4 := by 
      nlinarith [eq4, hy2']
    
    left
    linarith