import Mathlib

open Real Set

theorem algebra_321448 :
    IsLeast {x | ∃ a b : ℝ, x = a^2 + b^2 + a * b + a + b} (-1 / 3) ∧
    IsLeast {x | ∃ a b c : ℝ, x = a^2 + b^2 + c^2 + a * b + b * c + c * a + a + b + c} (-3 / 8) ∧
    IsLeast {x | ∃ a b c d : ℝ, x = a^2 + b^2 + c^2 + d^2 + a * b + a * c + a * d + b * c + b * d + c * d + a + b + c + d} (-2 / 5) := by
  constructor
  · -- Prove that -1/3 is the minimum for the 2-variable expression
    constructor
    · -- Show that -1/3 is indeed a possible value
      use -1/3, -1/3
      norm_num
    · -- Show that -1/3 is the minimum
      intro x hx
      rcases hx with ⟨a, b, hx⟩
      nlinarith [sq_nonneg (a + b + 1/3), sq_nonneg (a - b), sq_nonneg (a + 1/3), sq_nonneg (b + 1/3)]
  constructor
  · -- Prove that -3/8 is the minimum for the 3-variable expression
    constructor
    · -- Show that -3/8 is indeed a possible value
      use -1/4, -1/4, -1/4
      norm_num
    · -- Show that -3/8 is the minimum
      intro x hx
      rcases hx with ⟨a, b, c, hx⟩
      nlinarith [sq_nonneg (a + b + c + 3/4), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (a + 1/4), sq_nonneg (b + 1/4), sq_nonneg (c + 1/4)]
  · -- Prove that -2/5 is the minimum for the 4-variable expression
    constructor
    · -- Show that -2/5 is indeed a possible value
      use -1/5, -1/5, -1/5, -1/5
      norm_num
    · -- Show that -2/5 is the minimum
      intro x hx
      rcases hx with ⟨a, b, c, d, hx⟩
      nlinarith [sq_nonneg (a + b + c + d + 4/5), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + 1/5), sq_nonneg (b + 1/5), sq_nonneg (c + 1/5), sq_nonneg (d + 1/5)]