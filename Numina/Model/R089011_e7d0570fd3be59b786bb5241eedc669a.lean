import Mathlib

theorem algebra_21069 (x : ℚ) :
    2*x^3-9*x^2-32*x-21=0 ↔ x=-3/2 ∨ x=-1 ∨ x=7 := by
  constructor
  · -- Assume 2 * x^3 - 9 * x^2 - 32 * x - 21 = 0, prove x = -3/2 ∨ x = -1 ∨ x = 7
    intro h
    have h1 : (x + 3/2) * (x + 1) * (x - 7) = 0 := by
      nlinarith [h]
    cases' (mul_eq_zero.mp h1) with h2 h3
    · cases' (mul_eq_zero.mp h2) with h4 h5
      · left
        linarith
      · right
        left
        linarith
    · right
      right
      linarith
  · -- Assume x = -3/2 ∨ x = -1 ∨ x = 7 prove 2 * x^3 - 9 * x^2 - 32 * x - 21 = 0
    rintro (h | h | h)
    · rw [h]
      norm_num
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  all_goals nlinarith