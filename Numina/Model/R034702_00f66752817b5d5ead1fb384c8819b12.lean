import Mathlib

theorem algebra_247019 (x : ℝ) (hx : x ≠ 1 ∧ x ≠ -2) :
    2 * x / (x - 1) - x / (x + 2) - 5 * x / ((x - 1) * (x + 2)) =
    4 / (x ^ 2 + x - 2) - 2 / (x - 1) ↔ x = 0 := by
  constructor
  · -- Assume the equation holds, we need to prove x = 0
    intro heq
    have h1 : x - 1 ≠ 0 := by
      intro h
      apply hx.1
      linarith
    have h2 : x + 2 ≠ 0 := by
      intro h
      apply hx.2
      linarith
    have h3 : (x - 1) * (x + 2) ≠ 0 := by
      apply mul_ne_zero
      exact h1
      exact h2
    have h4 : x ^ 2 + x - 2 = (x - 1) * (x + 2) := by
      ring
    have eq1 : 2 * x / (x - 1) - x / (x + 2) - 5 * x / ((x - 1) * (x + 2)) =
        x ^ 2 / ((x - 1) * (x + 2)) := by 
      field_simp [(show x - 1 ≠ 0 by exact h1), (show x + 2 ≠ 0 by exact h2), 
        (show (x - 1) * (x + 2) ≠ 0 by exact h3)]
      ring
    have eq2 : 4 / (x ^ 2 + x - 2) - 2 / (x - 1) =
        -2 * x / ((x - 1) * (x + 2)) := by 
      rw [h4]
      field_simp [(show x - 1 ≠ 0 by exact h1), (show x + 2 ≠ 0 by exact h2), 
        (show (x - 1) * (x + 2) ≠ 0 by exact h3)]
      ring
    rw [eq1, eq2] at heq
    have heq2 : x ^ 2 = -2 * x := by
      field_simp [(show (x - 1) * (x + 2) ≠ 0 by exact h3)] at heq
      linarith
    have heq3 : x * (x + 2) = 0 := by
      linarith [heq2]
    cases' (mul_eq_zero.1 heq3) with h4 h5
    · -- Case x = 0 
      linarith 
    · -- Case x + 2 = 0, so x = -2
      exfalso 
      apply hx.2
      linarith
  · -- Assume x = 0, prove the equation
    intro heq
    rw [heq]
    norm_num