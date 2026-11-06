import Mathlib

theorem algebra_6310
    {x : ℝ}
    (hx : x ≠ 0)
    (hx1 : x + 1/x = -2) :
    x^2021 + 1/x^2021 = -2 := by
  have h1 : x^2 + 2 * x + 1 = 0 := by 
    field_simp [hx] at hx1
    nlinarith

  have h2 : (x + 1) ^ 2 = 0 := by
    nlinarith
  
  have hx_eq : x + 1 = 0 := by
    apply pow_eq_zero 
    exact h2
  
  have h3 : x = -1 := by 
    linarith
  
  rw [h3]
  norm_num