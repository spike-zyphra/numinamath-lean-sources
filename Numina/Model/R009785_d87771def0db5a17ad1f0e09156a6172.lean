import Mathlib

theorem algebra_9148 (x : ℝ) (a b : ℝ × ℝ × ℝ)
    (ha : a = (3, x ^ 2 + 2, 3)) (hb : b = (x - 4, 2, x)) :
    a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2 = 0 ↔
    x = -4 ∨ x = 1 := by
  rw [ha, hb]
  constructor
  · -- Assume the dot product is zero, prove the disjunction about x
    intro h
    simp at h
    -- We get the equation 2x^2 + 6x - 8 = 0
    have h1 : 2 * x ^ 2 + 6 * x - 8 = 0 := by 
      linarith
    -- Solving the quadratic equation
    have : (x - 1) * (2 * x + 8) = 0 := by 
      nlinarith [h1]
    cases' (mul_eq_zero.mp this) with h2 h3
    · -- Case where x - 1 = 0, so x = 1
      right
      linarith
    · -- Case where 2x + 8 = 0, so x = -4
      left
      linarith
  · -- Assume the disjunction about x, prove the dot product is zero
    rintro (h | h)
    · -- Case where x = -4
      rw [h]
      norm_num
    · -- Case where x = 1
      rw [h]
      norm_num