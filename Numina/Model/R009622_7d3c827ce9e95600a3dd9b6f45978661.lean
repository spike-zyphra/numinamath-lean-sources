import Mathlib

theorem algebra_9278 (x : ℝ) : 2*x^2-5*x+2=0 ↔
    x = 2 ∨ x = 1/2 := by
  constructor
  · -- Forward direction: assume 2x^2-5x+2=0, prove x=2 or x=1/2
    intro h
    have h1 : 2 * x^2 - 5 * x + 2 = 0 := by linarith
    have h2 : (x - 2) * (2 * x - 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where x - 2 = 0, so x = 2
      left
      linarith
    · -- Case where 2x - 1 = 0, so x = 1/2
      right
      linarith
  · -- Backward direction: assume x=2 or x=1/2, prove 2x^2-5x+2=0
    rintro (h | h)
    · -- Case x=2
      rw [h]
      norm_num
    · -- Case x=1/2
      rw [h]
      norm_num