import Mathlib

theorem algebra_15005 : IsGreatest {t : ℝ | ∃ a b c d, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 4 ∧ t = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3} 8 := by
  constructor
  · -- Show 8 is in the set
    use 2, 0, 0, 0
    norm_num
  · -- Show 8 is an upper bound
    intro t ht
    rcases ht with ⟨a, b, c, d, h1, h2⟩
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (d - 2),
              sq_nonneg (a + 2), sq_nonneg (b + 2), sq_nonneg (c + 2), sq_nonneg (d + 2)]