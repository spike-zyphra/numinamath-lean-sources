import Mathlib

theorem algebra_273279 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : (x + 200) * (y / 2) = x * y) (h2 : (x + 25) * (y * 2) = x * y) :
    y = 10 := by
  have h4 : y ≠ 0 := by nlinarith
  have h3 : x + 200 = 2 * x := by
    have h4 : y ≠ 0 := by nlinarith 
    have h_eq : (x + 200) * (y / 2) = x * y := h1 
    have h_eq2 : (x + 200) * y = 2 * x * y := by 
      nlinarith [h_eq] 
    have h_eq3 : x + 200 = 2 * x := by 
      apply (mul_left_inj' h4).mp 
      linarith 
    linarith 
  have hx_eq : x = 200 := by 
    linarith 
  rw [hx_eq] at h2
  nlinarith