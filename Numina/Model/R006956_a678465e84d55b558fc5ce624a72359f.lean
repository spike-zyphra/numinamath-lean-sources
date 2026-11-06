import Mathlib
theorem algebra_609351 : IsLeast {y : ℝ | ∃ x : ℝ, (y + x) = (y - x) ^ 2 + 3 * (y - x) + 3} (-1 / 2):= by
  constructor
  · -- Let's verify that y = -1/2 is achievable, with x = 3/2
    use 3 / 2
    norm_num
  · -- We need to show y >= -1/2 for all y in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    nlinarith [sq_nonneg (y - x + 2), sq_nonneg (y + 1 / 2), sq_nonneg (x - 3 / 2)]