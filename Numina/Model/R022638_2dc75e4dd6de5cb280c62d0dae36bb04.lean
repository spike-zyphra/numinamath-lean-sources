import Mathlib

theorem algebra_203249 (x y a : ℝ) (h₀ : x + y = a) (h₁ : x^3 + y^3 = a)
    (h₂ : x^5 + y^5 = a) :
    a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 := by
  have eq1 : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
    ring
  rw [h₀] at eq1
  rw [h₁] at eq1
  have eq2 : a * (a^2 - 3 * (x * y) - 1) = 0 := by
    nlinarith
  by_cases ha : a = 0
  · -- If a = 0, then this is valid.
    simp [ha]
  · -- Case $a ≠ 0$
    have eq3 : x * y = (a^2 - 1) / 3 := by
      have h3 : a^2 - 3 * (x * y) - 1 = 0 := by
        apply (mul_left_inj' (show a ≠ 0 by assumption)).mp
        linarith [eq2]
      linarith
    have eq4 : x^5 + y^5 = (x + y)^5 - 5 * (x * y) * (x + y)^3 + 5 * (x * y)^2 * (x + y) := by
      ring
    rw [h₀, eq3] at eq4
    rw [h₂] at eq4
    have eq6 : a^4 - 5 * ((a^2 - 1) / 3) * a^2 + 5 * ((a^2 - 1) / 3)^2 - 1 = 0 := by
      apply (mul_left_inj' (show a ≠ 0 by assumption)).mp
      linarith [eq4]
    have eq7 : (a^2 - 4) * (a^2 - 1) = 0 := by
      nlinarith [sq_nonneg (a^2 - 3), sq_nonneg (a^2 - 3)]
    have eq8 : a^2 = 4 ∨ a^2 = 1 := by
      cases (mul_eq_zero.mp eq7) with
      | inl h =>
        left
        nlinarith
      | inr h =>
        right
        nlinarith
    cases eq8 with
    | inl h9 =>
      have eq10 : a = 2 ∨ a = -2 := by
        have h10 : a^2 = 4 := h9
        have : a = 2 ∨ a = -2 := by
          have h11 : a^2 - 4 = 0 := by linarith
          have h12 : (a - 2) * (a + 2) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h12) with h13 h14
          · left
            linarith
          · right
            linarith
        assumption
      tauto
    | inr h9 =>
      have eq10 : a = 1 ∨ a = -1 := by
        have h10 : a^2 = 1 := h9
        have : a = 1 ∨ a = -1 := by
          have h11 : a^2 - 1 = 0 := by linarith
          have h12 : (a - 1) * (a + 1) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h12) with h13 h14
          · left
            linarith
          · right
            linarith
        assumption
      tauto