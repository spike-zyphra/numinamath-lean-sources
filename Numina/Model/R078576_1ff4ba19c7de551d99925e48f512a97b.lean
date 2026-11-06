import Mathlib

theorem algebra_209259 (a b c d e : ℝ) (h₀ : a + b + c + d + e = 8) (h₁ : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    max (max (max (max a b) c) d) e ≤ 16 / 5 := by
  have h2 : a ≤ 16 / 5 := by
    nlinarith [sq_nonneg (b + c + d + e), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)
      , sq_nonneg (a - 16 / 5)]
  have h3 : b ≤ 16 / 5 := by
    nlinarith [sq_nonneg (a + c + d + e), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)
      , sq_nonneg (b - 16 / 5)]
  have h4 : c ≤ 16 / 5 := by
    nlinarith [sq_nonneg (a + b + d + e), sq_nonneg (a - b), sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (d - e)
      , sq_nonneg (c - 16 / 5)]
  have h5 : d ≤ 16 / 5 := by
    nlinarith [sq_nonneg (a + b + c + e), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - e), sq_nonneg (c - e)
      , sq_nonneg (d - 16 / 5)]
  have h6 : e ≤ 16 / 5 := by
    nlinarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)
      , sq_nonneg (e - 16 / 5)]
  have h7 : max (max (max (max a b) c) d) e ≤ 16 / 5 := by
    simp [max_le_iff, h2, h3, h4, h5, h6]
    all_goals linarith
  linarith