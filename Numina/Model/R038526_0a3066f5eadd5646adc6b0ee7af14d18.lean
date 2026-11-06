import Mathlib

theorem algebra_45145 :
    IsLeast {a | ∃ b : ℝ, a ^ 4 + 2 * a ^ 2 * b + 2 * a * b + b ^ 2 = 960} (-8) := by
  constructor
  · -- Show that -8 is in the set
    use -56
    norm_num
  · -- Show that -8 is the smallest
    intro a
    rintro ⟨b, hb⟩
    nlinarith [sq_nonneg (a ^ 2 + b + 8), sq_nonneg (a + 8), sq_nonneg (a ^ 2 - 16), sq_nonneg (b - 2 * a - 8), sq_nonneg (2 * a + 16), sq_nonneg (a + 8 - b), sq_nonneg (a + 8), sq_nonneg (a + 8 - b / 8), sq_nonneg (b + 56), sq_nonneg (b + 56), sq_nonneg (b + 56), sq_nonneg (a + 8)]