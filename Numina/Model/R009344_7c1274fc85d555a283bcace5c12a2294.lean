import Mathlib

theorem algebra_8978 (x : ℝ) : (x - 2) * (x - 3) = x - 2 ↔ x = 4 ∨ x = 2 := by
  constructor
  · -- Proof of the forward direction
    intro h
    by_cases h1 : x - 2 = 0
    · -- Case where x - 2 = 0 (so x = 2)
      right
      linarith
    · -- Case where x - 2 ≠ 0
      have h2 : (x - 2) * (x - 4) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h2) with h3 h4
      · -- Contradiction if x - 2 = 0
        exfalso
        exact h1 (by linarith)
      · -- Therefore x - 4 = 0
        left
        linarith
  · -- Proof of the reverse direction
    rintro (h | h)
    · -- If x = 4, verify the equation
      rw [h]
      norm_num
    · -- If x = 2, verify the equation
      rw [h]
      norm_num