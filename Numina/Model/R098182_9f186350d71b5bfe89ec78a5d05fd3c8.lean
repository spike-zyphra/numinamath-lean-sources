import Mathlib

theorem algebra_4263 {x : ℝ} (hx : x^3 - x + 1 = 0) :
    x^4 + 2 * x + 1 / x^2 = 1 := by 
  have h1 : x ≠ 0 := by 
    by_contra h
    rw [h] at hx 
    norm_num at hx 
  have h3 : x^3 = x - 1 := by linarith 
  have h4 : x^4 = x^2 - x := by 
    calc 
      x^4 = x * x^3 := by ring 
      _ = x * (x - 1) := by rw [h3]
      _ = x^2 - x := by ring 
  have h7 : x ^ 2 + 1 / x = 1 := by 
    have h8 : x ≠ 0 := h1 
    field_simp [h8] at *
    nlinarith 
  have h6 : (x ^ 2 + 1 / x) ^ 2 = 1 := by 
    rw [h7]
    all_goals norm_num 
  have h9 : x^4 + 2 * x + 1 / x^2 = (x ^ 2 + 1 / x) ^ 2 := by 
    field_simp [show x ≠ 0 from h1]
    ring 
  rw [h9]
  linarith [h6]