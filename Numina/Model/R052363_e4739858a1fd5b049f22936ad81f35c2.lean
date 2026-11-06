import Mathlib

theorem algebra_2560 {a b : ℝ} (h : a ≠ b) : -a / (a - b) = a / (b - a) := by
  have h1 : a - b ≠ 0 := by
    intro h2
    apply h
    linarith
  have h2 : b - a ≠ 0 := by
    intro h3
    have h4 : a - b = 0 := by linarith
    contradiction
  field_simp [h1, h2]
  <;> ring