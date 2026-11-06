import Mathlib

theorem inequalities_220312 (a b c : ℝ) (h : a > b ∧ b > c) :
    a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) > 0 := by
  have h1 : a > b := h.1
  have h2 : b > c := h.2
  have h3 : a > c := by linarith
  have h4 : a - b > 0 := by linarith
  have h5 : a - c > 0 := by linarith
  have h6 : b - c > 0 := by linarith
  have h7 : a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) =
      (a - b) * (a - c) * (b - c) := by
    ring
  rw [h7]
  have h8 : (a - b) * (a - c) * (b - c) > 0 := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
    all_goals linarith
    all_goals linarith
  linarith