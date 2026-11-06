import Mathlib

theorem algebra_325563 (x : ℝ) :
    36*x^4-84*x^3+37*x^2+14*x-3=0 ↔
    x=-1/3 ∨ x=3/2 ∨ x=1 ∨ x=1/6 := by
  constructor
  · -- Assume 36*x^4-84*x^3+37*x^2+14*x-3=0, prove the disjunction
    intro h
    have h1 : (3 * x + 1) * (2 * x - 3) * (x - 1) * (6 * x - 1) = 0 := by
      nlinarith [h]
    cases' (mul_eq_zero.mp h1) with h2 h3
    cases' (mul_eq_zero.mp h2) with h4 h5
    cases' (mul_eq_zero.mp h4) with h6 h7
    · -- Case 3 * x + 1 = 0
      left
      linarith
    · -- Case 2 * x - 3 = 0
      right
      left
      linarith
    · -- Case x - 1 = 0
      right
      right
      left
      linarith
    · -- Case 6 * x - 1 = 0
      right
      right
      right
      linarith
  · -- Assume the disjunction, prove 36*x^4-84*x^3+37*x^2+14*x-3=0
    rintro (h | h | h | h)
    · -- Case x = -1/3
      rw [h]
      norm_num
    · -- Case x = 3/2
      rw [h]
      norm_num
    · -- Case x = 1
      rw [h]
      norm_num
    · -- Case x = 1/6
      rw [h]
      norm_num