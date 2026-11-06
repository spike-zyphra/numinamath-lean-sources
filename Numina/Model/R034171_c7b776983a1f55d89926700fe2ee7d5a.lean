import Mathlib

theorem algebra_48137 {x y a b : ℝ} (h₀ : x + y = a + b) (h₁ : x^2 + y^2 = a^2 + b^2)
    (n : ℕ) : x^n + y^n = a^n + b^n := by
  have h4 : x * y = a * b := by
    have h5 : (x + y) ^ 2 = (a + b) ^ 2 := by 
      rw [h₀]
    nlinarith 
  have h5 : (x - a) * (x - b) = 0 := by 
    have h6 : y = a + b - x := by 
      linarith 
    have h7 : x * (a + b - x) = a * b := by 
      rw [show y = a + b - x by linarith [h6] ] at h4 
      linarith 
    nlinarith [sq_nonneg (x - a), sq_nonneg (x - b), sq_nonneg (y - a), sq_nonneg (y - b), sq_nonneg (x - y), sq_nonneg (a - b)]
  cases' (mul_eq_zero.mp h5) with h6 h7 
  · -- x - a = 0 i.e. x = a 
    have hx : x = a := by linarith 
    have hy : y = b := by 
      have h8 : x + y = a + b := h₀ 
      rw [hx] at h8 
      linarith 
    rw [hx, hy] 
    all_goals ring 
  · -- x - b = 0 i.e. x = b 
    have hx : x = b := by linarith 
    have hy : y = a := by 
      have h8 : x + y = a + b := h₀ 
      rw [hx] at h8 
      linarith 
    rw [hx, hy] 
    all_goals ring