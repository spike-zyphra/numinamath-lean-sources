import Mathlib

def f (x y : ℝ) := x ^ 2 * y - x * y ^ 2

theorem algebra_94358 :
    {(x, y) : ℝ × ℝ | f x y = f y x} =
    {(x, y) : ℝ × ℝ | x = 0 ∨ y = 0 ∨ x = y} := by
  ext ⟨x, y⟩
  simp [f]
  constructor
  · -- Assume h : x²y - xy² = y²x - yx², prove x = 0 ∨ y = 0 ∨ x = y
    intro h
    have h1 : x * y * (x - y) = 0 := by
      linarith [h]
    cases' (mul_eq_zero.mp h1) with h2 h3
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case h4: x = 0
      left
      exact h4
    · -- Case h5: y = 0
      right
      left
      exact h5
    · -- Case h3: x - y = 0
      right
      right
      linarith
  · -- Now the reverse direction
    rintro (h | h | h)
    · -- Case x = 0
      rw [show x = 0 by linarith]
      ring
    · -- Case y = 0
      rw [show y = 0 by linarith]
      ring
    · -- Case x = y
      have h2 : y = x := by linarith
      rw [show y = x by linarith]
      all_goals ring