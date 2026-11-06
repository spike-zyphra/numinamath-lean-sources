import Mathlib

theorem algebra_303537 {p : ℝ} (h : ∃ x1 x2, x1 ≠ x2 ∧ x1^2 - 2 * (p + 1) * x1 + p^2 + 8 = 0 ∧
    x2^2 - 2 * (p + 1) * x2 + p^2 + 8 = 0 ∧ |x1 - x2| = 2) : p = 4 := by
  rcases h with ⟨x1, x2, h12, h1, h2, h3⟩
  have h4 : (x1 - x2)^2 = 4 := by 
    cases eq_or_eq_neg_of_abs_eq h3 with
    | inl h5 =>
      -- case where x1 - x2 = 2
      nlinarith
    | inr h6 =>
      -- case where x1 - x2 = -2
      nlinarith
  have h5 : x1 + x2 = 2 * (p + 1) := by
    -- subtract the two equations
    have eq1 : x1^2 - x2^2 - 2 * (p + 1) * (x1 - x2) = 0 := by linarith 
    have h12' : x1 - x2 ≠ 0 := sub_ne_zero_of_ne h12
    -- factor the equation
    have eq2 : (x1 - x2) * (x1 + x2 - 2 * (p + 1)) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 eq2) with h6 h7
    · -- h6 is x1 - x2 = 0, but they're different
      exfalso
      exact h12 (by linarith)
    · -- h7 is x1 + x2 - 2 * (p + 1) = 0
      linarith
  have h7 : x1 * x2 = p^2 + 8 := by
    nlinarith [h1, h5]
  -- connect h4 with h5, h7 using the identity (x1 - x2)^2 = (x1 + x2)^2 - 4 * (x1 * x2)
  have h6 : (x1 + x2)^2 - 4 * (x1 * x2) = 4 := by 
    nlinarith [h4]
  rw [show (x1 + x2) = 2 * (p + 1) by linarith [h5], show (x1 * x2) = p^2 + 8 by linarith [h7]] at h6
  nlinarith