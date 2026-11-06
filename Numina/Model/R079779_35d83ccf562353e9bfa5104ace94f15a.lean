import Mathlib

theorem algebra_218327 :
    IsLeast {x | ∃ a b : ℝ, x = a^2 + 4 * b^2 - 2 * a ∧ 2 * a + 8 * b = 3} (-19 / 20) := by
  constructor
  · -- Show that -19/20 is achievable
    use 11 / 10, 1 / 10
    constructor
    · -- Show x = -19/20
      norm_num
    · -- Show 2 * a + 8 * b = 3
      norm_num
  · -- Show that -19/20 is indeed the least
    intro x hx
    rcases hx with ⟨a, b, h_eq, h_eq2⟩
    have h1 : b = (3 - 2 * a) / 8 := by
      linarith
    rw [h1] at h_eq
    nlinarith [sq_nonneg (a - 11 / 10), sq_nonneg (b - 1 / 10)]