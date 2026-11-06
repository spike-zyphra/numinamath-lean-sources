import Mathlib

theorem algebra_223636 (k : ℝ) (h : (7 - k) * 2 * k = 3 * k + 9) :
    k = 9 / 2 ∨ k = 1 := by 
  have h1 : 2 * k ^ 2 - 11 * k + 9 = 0 := by 
    nlinarith 
  have h2 : (2 * k - 9) * (k - 1) = 0 := by
    nlinarith 
  cases (mul_eq_zero.1 h2) with
  | inl h3 =>
    -- 2k - 9 = 0
    have hk : k = 9 / 2 := by 
      linarith 
    left 
    exact hk 
  | inr h4 =>
    -- k - 1 = 0 
    have hk : k = 1 := by 
      linarith 
    right 
    exact hk