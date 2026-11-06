import Mathlib

theorem algebra_291883 (a b c : ℝ)
    (h₀ : a^2 + a * b + c = 0)
    (h₁ : b^2 + b * c + a = 0)
    (h₂ : c^2 + c * a + b = 0) :
    (a, b, c) = (0, 0, 0) ∨ (a, b, c) = (-1 / 2, -1 / 2, -1 / 2) := by

  -- Subtract the second equation from the first.
  have h3 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- Since squared terms are non-negative, their sum is zero only if each term is zero.
  have ha1 : a - b = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hb1 : b - c = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hc1 : c - a = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- From the above equations, variables must be equal.
  have h4 : a = b := by 
    linarith 
  have h5 : b = c := by 
    linarith 
  have h6 : a = c := by 
    linarith 
  -- Substitute that variables are equal into the first equation.
  have h7 : 2 * a ^ 2 + a = 0 := by
    rw [show b = a by linarith [h4], show c = a by linarith [h6]] at h₀ 
    nlinarith 
  -- Factoring gives us a = 0 or a = -1/2.
  have h8 : a * (2 * a + 1) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.1 h8) with ha2 ha3 
  · -- Case where a = 0 
    have ha0 : a = 0 := by linarith 
    have hb0 : b = 0 := by linarith [h4, ha0] 
    have hc0 : c = 0 := by linarith [h5, hb0] 
    left 
    simp [ha0, hb0, hc0] 
  · -- Case where 2a + 1 = 0, so a = -1/2 
    have ha1_2 : a = -1 / 2 := by linarith 
    have hb1_2 : b = -1 / 2 := by linarith [h4, ha1_2] 
    have hc1_2 : c = -1 / 2 := by linarith [h5, hb1_2] 
    right 
    simp [ha1_2, hb1_2, hc1_2]