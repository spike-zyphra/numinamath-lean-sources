import Mathlib

theorem inequalities_603580 {a b c : ℝ} (ha : a > b) (hb : b > c) :
    a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) > 0 := by
  have h1 : a - b > 0 := by linarith
  have h2 : b - c > 0 := by linarith
  have h3 : a - c > 0 := by linarith [ha, hb]
  have h4 : a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) = (a - b) * (a - c) * (b - c) := by
    ring
  rw [h4]
  apply mul_pos
  · -- Multiply (a-b) * (a-c) > 0
    apply mul_pos
    · -- a-b > 0
      linarith
    · -- a-c > 0
      linarith [ha, hb]
  · -- b-c > 0
    linarith [hb]