import Mathlib

def f (x y : ℝ) := x^2 * y - x * y^2

theorem algebra_314229 :
    {(x, y) : ℝ × ℝ | f x y = f y x} =
    {(x, y) : ℝ × ℝ | x = 0 ∨ y = 0 ∨ x = y} := by
  ext ⟨x, y⟩
  simp [f]
  constructor
  · -- Assume x * y = y * x
    intro h
    have h1 : x * y * (x - y) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case where x = 0
      left
      exact h4
    · -- Case where y = 0
      right
      left
      exact h5
    · -- Case where x - y = 0, i.e., x = y
      right
      right
      linarith
  · -- Show that if x = 0 or y = 0 or x = y, then x * y = y * x
    rintro (h | h | h)
    · -- Case where x = 0
      rw [h]
      ring
    · -- Case where y = 0
      rw [h]
      ring
    · -- Case where x = y
      have h1 : x = y := h
      rw [show y = x by linarith [h1]]
      all_goals ring