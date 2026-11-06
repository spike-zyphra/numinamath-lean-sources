import Mathlib

theorem algebra_166318 {x y : ℝ} (h₀ : x^3 + 3 * x * y^2 = 158) (h₁ : 3 * x^2 * y + y^3 = -185) :
    (x, y) = (2, -5) := by
  have h3 : (x + y) ^ 3 = -27 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 2), sq_nonneg (y + 5)]
  have h2 : x + y = -3 := by
    have h4 : (x + y) ^ 3 + 27 = (0 : ℝ) := by
      linarith 
    have h9 : (x + y + 3) * ((x + y) ^ 2 - (x + y) * 3 + 9) = 0 := by
      nlinarith 
    cases (mul_eq_zero.1 h9) with
    | inl h10 => 
      linarith
    | inr h11 => 
      nlinarith [sq_nonneg ((x + y) - 3 / 2), sq_nonneg (y), sq_nonneg (x)]
  have h2_y : y = -3 - x := by 
    linarith
  rw [h2_y] at h₀ 
  have h4_eq : (x - 2) * (4 * x ^ 2 + 26 * x + 79) = 0 := by
    nlinarith [sq_nonneg (x + 2), sq_nonneg ((-3 - x) + 5)]
  cases (mul_eq_zero.1 h4_eq) with
  | inl h5_eq => 
    have hx2 : x = 2 := by 
      linarith 
    have hy5 : y = -5 := by
      rw [hx2] at h2_y 
      linarith 
    simp [hx2, hy5] 
  | inr h6_eq => 
    nlinarith [sq_nonneg (x + 26 / 8), sq_nonneg (y), sq_nonneg (y + 5)]