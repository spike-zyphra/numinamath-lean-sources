import Mathlib

theorem algebra_13263 : IsLeast {x | ∃ a b : ℝ, x = 4 * a ^ 2 - 4 * a * b + 6 * b ^ 2 - 12 * a - 4 * b + 36} 22 := by
  constructor
  · -- Show that 22 is indeed achievable, with a = 2, b = 1
    use 2, 1
    norm_num
  · -- Show that 22 is a lower bound
    intro x
    rintro ⟨a, b, rfl⟩
    nlinarith [sq_nonneg (2 * a - b - 3), sq_nonneg (b - 1), sq_nonneg (a - 2), sq_nonneg (b - 1)]