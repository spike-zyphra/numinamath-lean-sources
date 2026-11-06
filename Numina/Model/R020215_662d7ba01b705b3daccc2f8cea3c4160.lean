import Mathlib

theorem number_theory_105619 (x : ℝ) :
    (x - 2) * (x - 5) = 0 ↔ x = 2 ∨ x = 5 := by
  constructor
  · -- Assume (x - 2) * (x - 5) = 0, prove x = 2 ∨ x = 5
    intro h
    cases' (mul_eq_zero.mp h) with h1 h2
    · -- Case where x - 2 = 0, so x = 2
      left
      linarith
    · -- Case where x - 5 = 0, so x = 5
      right
      linarith
  · -- Assume x = 2 ∨ x = 5, prove (x - 2) * (x - 5) = 0
    rintro (h | h)
    · -- Case where x = 2
      rw [h]
      norm_num
    · -- Case where x = 5
      rw [h]
      norm_num