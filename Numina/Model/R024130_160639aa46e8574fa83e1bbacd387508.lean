import Mathlib

theorem algebra_155462 (a b c : ℝ) (h₀ : abs a ≥ abs (b + c)) (h₁ : abs b ≥ abs (c + a))
    (h₂ : abs c ≥ abs (a + b)) : a + b + c = 0 := by
  have h3 : a ^ 2 ≥ (b + c) ^ 2 := by 
    apply sq_le_sq.mpr
    exact h₀
  have h4 : b ^ 2 ≥ (c + a) ^ 2 := by
    apply sq_le_sq.mpr
    exact h₁
  have h5 : c ^ 2 ≥ (a + b) ^ 2 := by
    apply sq_le_sq.mpr
    exact h₂
  have h7 : (a + b + c) ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b - c), sq_nonneg (b - c - a), sq_nonneg (c - a - b)]
  have h8 : (a + b + c) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h9 : (a + b + c) ^ 2 = 0 := by
    linarith
  have h10 : a + b + c = 0 := by
    nlinarith
  exact h10