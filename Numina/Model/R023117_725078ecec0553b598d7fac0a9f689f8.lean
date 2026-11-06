import Mathlib

theorem inequalities_305794 :
    IsGreatest {x | ∃ a b c : ℝ, a ≥ b ∧ b ≥ c ∧ c > 0 ∧ a + b + c ≤ 4 ∧ x = a^2 + 3 * b^2 + 5 * c^2} 16 := by
  constructor
  · -- Show that 16 is in the set.
    use 4 / 3, 4 / 3, 4 / 3
    norm_num
  · -- Show that 16 is the greatest element in the set.
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2, hc0, h3, hx⟩
    nlinarith [sq_nonneg (a - 4 / 3), sq_nonneg (b - 4 / 3), sq_nonneg (c - 4 / 3),
      h1, h2, hc0, h3, mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ b - c by linarith)]