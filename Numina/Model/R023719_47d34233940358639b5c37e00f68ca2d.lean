import Mathlib

theorem algebra_224107 :
    IsLeast {d : ℝ | ∃ x y, d = x ^ 2 + y ^ 2 ∧ (x + 5) ^ 2 + (y - 12) ^ 2 = 14 ^ 2} 1 := by
  constructor
  · -- First we'll show 1 is in the set
    use 5 / 13, -12 / 13
    norm_num
  · -- Now we need to show 1 is the smallest element in the set
    intro d h
    rcases h with ⟨x, y, h_eq, h_eq1⟩
    have h1 : x ^ 2 + y ^ 2 ≥ 1 := by
      nlinarith [sq_nonneg (x * 12 - y * 5), sq_nonneg (x + 5 / 13), sq_nonneg (y + 12 / 13),
        sq_nonneg (x - 5 / 13), sq_nonneg (y + 12 / 13), sq_nonneg (x + 5), sq_nonneg (y - 12),
        sq_nonneg (x * 5 + y * 12), mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)]
    linarith [h_eq, h1]