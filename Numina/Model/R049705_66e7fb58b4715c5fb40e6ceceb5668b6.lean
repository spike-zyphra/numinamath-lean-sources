import Mathlib

theorem algebra_97575 : {(x, y) : ℝ × ℝ | (x + y)^2 = x^2 + y^2} = {(x, y) | x = 0 ∨ y = 0} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x + y)² = x² + y², prove x = 0 ∨ y = 0
    intro h
    have h1 : x * y = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case where x = 0
      left
      linarith
    · -- Case where y = 0
      right
      linarith
  · -- Assume x = 0 ∨ y = 0, prove (x + y)² = x² + y²
    rintro (h | h)
    · -- Case where x = 0
      rw [h]
      nlinarith
    · -- Case where y = 0
      rw [h]
      nlinarith