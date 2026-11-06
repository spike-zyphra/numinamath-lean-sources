import Mathlib

theorem algebra_171158 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h₀ : b = 1.5 * a) (h₁ : 0 < 2) (h₂ : 0 < 1.5) :
    ∃ x, x > 0 ∧ (1 - x / 2) * a = (1 - x / 1.5) * b := by
  use 1
  constructor
  · norm_num
  · rw [h₀]
    ring_nf
    <;> simp [mul_add, mul_sub] at *
    all_goals
      ring_nf