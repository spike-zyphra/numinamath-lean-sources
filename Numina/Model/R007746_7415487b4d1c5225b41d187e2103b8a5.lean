import Mathlib
theorem algebra_9358 (x : ℝ) : x^2 = 2 * x ↔ x = 0 ∨ x = 2 := by
  constructor
  · -- Forward direction: x^2 = 2 * x → x = 0 ∨ x = 2
    intro h
    have h1 : x^2 - 2 * x = 0 := by linarith
    have h2 : x * (x - 2) = 0 := by
      linarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where h3 : x = 0
      left
      exact h3
    · -- Case where h4 : x - 2 = 0, which is equivalent to x = 2
      right
      linarith
  · -- Backward direction: x = 0 ∨ x = 2 → x^2 = 2 * x
    rintro (h | h)
    · -- Case where h : x = 0
      rw [h]
      norm_num
    · -- Case where h : x = 2
      rw [h]
      norm_num