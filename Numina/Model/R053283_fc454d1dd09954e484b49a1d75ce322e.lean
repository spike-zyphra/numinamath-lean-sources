import Mathlib

theorem inequalities_601036 (a b c : ℝ) (ha : a > b) (hb : b > c) :
    a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) > 0 := by
  have h1 : a > c := by linarith
  have h2 : a - b > 0 := by linarith
  have h3 : b - c > 0 := by linarith
  have h4 : a - c > 0 := by linarith
  have h5 : a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) =
      (a - b) * (b - c) * (a - c) := by 
    ring
  rw [h5]
  have h6 : (a - b) * (b - c) * (a - c) > 0 := by 
    apply mul_pos
    apply mul_pos
    all_goals
      linarith
  linarith