import Mathlib

theorem algebra_8135 {x : ℝ} (hx : x^2-3*x+1=0) :
    x^2/(x^4+x^2+1) = 1/8 := by

  have h1 : x^2 = 3 * x - 1 := by linarith
  have h2 : x^4 = (21 * x - 8) := by 
    calc
      x^4 = (x^2)^2 := by ring
      _ = (3 * x - 1)^2 := by rw [h1]
      _ = 9 * (x^2) - 6 * x + 1 := by ring
      _ = 9 * (3 * x - 1) - 6 * x + 1 := by rw [h1]
      _ = 21 * x - 8 := by ring
  
  have h3 : x^4 + x^2 + 1 = 8 * x^2 := by 
    rw [h2, h1]
    linarith
  
  have hx2 : x^2 ≠ 0 := by
    by_contra h
    have h4 : x^2 = 0 := by linarith
    have h5 : x = 0 := by nlinarith
    rw [h5] at hx
    norm_num at hx
  
  rw [h3]
  field_simp [hx2]
  <;> nlinarith [h1]