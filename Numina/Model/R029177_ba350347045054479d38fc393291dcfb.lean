import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_611140:
  {(x, y) : ℝ × ℝ | x ^ 4 = x ^ 2 * y ^ 2} = {(x, y) | x= 0 ∨ x = y ∨ x = -y} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x^4 = x^2 * y^2), prove (x = 0 ∨ x = y ∨ x = -y)
    intro h
    have h1 : x ^ 2 * (x ^ 2 - y ^ 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case x^2 = 0, so x = 0
      left
      nlinarith
    · -- Case x^2 - y^2 = 0, so x^2 = y^2
      have h4 : (x - y) * (x + y) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- Case x - y = 0, so x = y
        right
        left
        linarith
      · -- Case x + y = 0, so x = -y
        right
        right
        linarith
  · -- Assume (x = 0 ∨ x = y ∨ x = -y), prove (x ^ 4 = x ^ 2 * y ^ 2)
    rintro (h | h | h)
    · -- Case x = 0
      rw [h]
      norm_num
    · -- Case x = y
      have h1 : y = x := by
        linarith
      rw [show y = x by linarith]
      all_goals nlinarith
    · -- Case x = -y
      have h1 : y = -x := by
        nlinarith
      rw [show y = -x by linarith]
      all_goals nlinarith