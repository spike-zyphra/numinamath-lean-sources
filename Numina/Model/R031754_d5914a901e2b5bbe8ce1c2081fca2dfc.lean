import Mathlib

theorem algebra_100095 :
  IsGreatest {x | ∃ a b c : ℝ, a + b = c - 1 ∧ a * b = c ^ 2 - 7 * c + 14 ∧ x = a ^ 2 + b ^ 2} 8 := by
  constructor
  · -- Show that 8 is in the set.
    use 2, 2, 5
    norm_num
  · -- Show that for any x in the set, x ≤ 8.
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2, h3⟩
    have h : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by
      ring
    have h4 : a ^ 2 + b ^ 2 = (c - 1) ^ 2 - 2 * (c ^ 2 - 7 * c + 14) := by
      rw [h]
      rw [h1]
      rw [h2]
    have h5 : a ^ 2 + b ^ 2 = -c ^ 2 + 12 * c - 27 := by
      nlinarith
    have h6 : x = -c ^ 2 + 12 * c - 27 := by
      linarith [h3, h5]
    nlinarith [sq_nonneg (c - 5), sq_nonneg (a - b), sq_nonneg (c - 7), sq_nonneg (a + b - c + 1)]