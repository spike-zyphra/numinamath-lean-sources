import Mathlib

theorem algebra_187106 {x y : ℝ} (h₀ : x^3 + y^3 = 9) (h₁ : x * y = 2) :
    (x, y) = (1, 2) ∨ (x, y) = (2, 1) := by
  have h2 : x + y = 3 := by
    have h3 : x^3 + y^3 = (x + y)^3 - 3 * (x * y) * (x + y) := by 
      ring
    rw [h₁] at h3 
    have h4 : x^3 + y^3 = (x + y)^3 - 6 * (x + y) := by
      linarith
    rw [h₀] at h4 
    have h5 : (x + y)^3 - 6 * (x + y) = 9 := by 
      linarith
    have h6 : (x + y)^3 - 6 * (x + y) - 9 = 0 := by 
      linarith
    have h7 : (x + y - 3) * ((x + y)^2 + 3 * (x + y) + 3) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- x+y -3 = 0
      linarith 
    · -- (x+y)^2 + 3*(x+y) +3 =0
      nlinarith [sq_nonneg ((x + y) + 3 / 2)]
  have h3 : y = 3 - x := by 
    nlinarith [h2]
  rw [h3] at h₁
  have h4 : x^2 - 3 * x + 2 = 0 := by 
    nlinarith 
  have h5 : (x - 1) * (x - 2) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- x=1
    have hx : x = 1 := by 
      linarith 
    have hy : y = 2 := by 
      nlinarith [h2, hx] 
    left 
    simp [hx, hy] 
  · -- x=2
    have hx : x = 2 := by 
      linarith 
    have hy : y = 1 := by 
      nlinarith [h2, hx] 
    right 
    simp [hx, hy]