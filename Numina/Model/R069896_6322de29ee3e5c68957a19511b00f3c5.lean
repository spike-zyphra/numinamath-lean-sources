import Mathlib

theorem algebra_15848 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + 1 / y = 10 ∧ y + 1 / x = 5 / 12) :
    x = 4 ∨ x = 6 := by
  have h₁ : x + 1 / y = 10 := hxy.1
  have h₂ : y + 1 / x = 5 / 12 := hxy.2
  
  have eq1 : x * y + 1 = 10 * y := by
    have h1 : y ≠ 0 := hy
    field_simp at h₁
    linarith
  
  have eq2 : x * y + 1 = (5 / 12) * x := by
    have h2 : x ≠ 0 := hx
    field_simp at h₂
    linarith
  
  have h3 : x * y - 10 * y = -1 := by 
    nlinarith
  
  have h4 : x * y - (5 / 12) * x = -1 := by 
    nlinarith
  
  have h_eq : 10 * y = (5 / 12) * x := by 
    nlinarith
  
  have h_eq2 : y = x / 24 := by 
    linarith
  
  have h7 : x^2 - 10 * x + 24 = 0 := by 
    rw [h_eq2] at h3 
    nlinarith [sq_nonneg (x), sq_nonneg (x - 4), sq_nonneg (x - 6)]
  
  have h7 : (x - 4) * (x - 6) = 0 := by 
    nlinarith
  
  cases' (mul_eq_zero.1 h7) with h8 h9
  · left
    linarith 
  · right 
    linarith