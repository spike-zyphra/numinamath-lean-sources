import Mathlib

theorem algebra_323258 {x y a b : ℝ} (h₀ : x + y = a + b) (h₁ : x ^ 2 + y ^ 2 = a ^ 2 + b ^ 2) :
    x ^ 2001 + y ^ 2001 = a ^ 2001 + b ^ 2001 := by
  have h2 : x * y = a * b := by
    have h3 : (x + y) ^ 2 = (a + b) ^ 2 := by 
      rw [h₀]
    have h4 : (x + y) ^ 2 = x^2 + 2 * x * y + y^2 := by
      nlinarith 
    have h5 : (a + b) ^ 2 = a^2 + 2 * a * b + b^2 := by
      nlinarith
    rw [h4, h5] at h3
    have h6 : x^2 + y^2 = a^2 + b^2 := h₁
    nlinarith
  have h9 : (x - y) ^ 2 = (a - b) ^ 2 := by 
    nlinarith [h₁, h2, sq_nonneg (x - y), sq_nonneg (a - b)]
  have h10 : x - y = a - b ∨ x - y = b - a := by
    have h11 : (x - y) ^ 2 - (a - b) ^ 2 = 0 := by 
      nlinarith [h9]
    have h12 : (x - y - (a - b)) * (x - y + (a - b)) = 0 := by 
      nlinarith [h11]
    cases (mul_eq_zero.1 h12) with
    | inl h13 =>
      left
      linarith 
    | inr h14 =>
      right
      linarith 
  rcases h10 with h11 | h11
  · -- Case where x - y = a - b
    have h12 : x = a := by 
      nlinarith [h₀, h11]
    have h13 : y = b := by
      nlinarith [h₀, h12]
    rw [h12, h13]
    all_goals
      ring
  · -- Case where x - y = b - a 
    have h12 : x = b := by
      nlinarith [h₀, h11]
    have h13 : y = a := by
      nlinarith [h₀, h12]
    rw [h12, h13]
    all_goals
      ring