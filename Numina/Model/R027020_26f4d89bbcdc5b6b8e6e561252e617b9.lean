import Mathlib

theorem algebra_261839 (x y a : ℝ) (h₀ : x + y = a) (h₁ : x ^ 3 + y ^ 3 = a)
    (h₂ : x ^ 5 + y ^ 5 = a) :
    a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 := by

  have eq1 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
    ring

  rw [h₀] at eq1
  have eq2 : a = a ^ 3 - 3 * (x * y) * a := by
    linarith [h₁, eq1]

  have eq3 : a * (1 - a ^ 2 + 3 * (x * y)) = 0 := by
    linarith [eq2]

  have eq4 : x ^ 5 + y ^ 5 = (x + y) ^ 5 - 5 * (x * y) * (x + y) ^ 3 + 5 * (x * y) ^ 2 * (x + y) := by
    ring

  rw [h₀] at eq4
  have eq5 : a = a ^ 5 - 5 * (x * y) * a ^ 3 + 5 * (x * y) ^ 2 * a := by
    linarith [h₂, eq4]

  have eq6 : a * (1 - a ^ 4 + 5 * (x * y) * a ^ 2 - 5 * (x * y) ^ 2) = 0 := by
    linarith [eq5]

  by_cases ha : a = 0
  · -- a = 0
    right
    right
    left
    exact ha
  · -- a ≠ 0
    have h3 : 1 - a ^ 2 + 3 * (x * y) = 0 := by
      apply (mul_right_inj' (show a ≠ 0 by
        intro ha'
        apply ha
        exact ha'
      )).mp
      linarith [eq3]

    have h4 : 1 - a ^ 4 + 5 * (x * y) * a ^ 2 - 5 * (x * y) ^ 2 = 0 := by
      apply (mul_right_inj' (show a ≠ 0 by
        intro ha'
        apply ha
        exact ha'
      )).mp
      linarith [eq6]

    have h6 : a ^ 2 = 1 ∨ a ^ 2 = 4 := by
      have h8 : x * y = (a ^ 2 - 1) / 3 := by
        nlinarith

      rw [h8] at h4
      have h9 : (a ^ 2 - 1) ^ 2 * (a ^ 2 - 4) = 0 := by
        nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (a ^ 2 - 4), sq_nonneg (a ^ 2), sq_nonneg ((a ^ 2 - 1) * a ^ 2), sq_nonneg ((a ^ 2 - 4) * a ^ 2)]
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- h10 : (a ^ 2 - 1) ^ 2 = 0
        have h12 : a ^ 2 - 1 = 0 := by
          apply pow_eq_zero 
          exact h10
        left
        nlinarith
      · -- h11 : a ^ 2 - 4 = 0
        right
        nlinarith

    cases h6 with
    | inl h15 =>
      have h16 : a = 1 ∨ a = -1 := by
        have h17 : a ^ 2 = 1 := h15
        rw [sq_eq_one_iff] at h17
        tauto
      cases h16 with
      | inl h18 =>
        right
        right
        right
        left
        exact h18
      | inr h18 =>
        right
        left
        exact h18
    | inr h15 =>
      have h18 : a = 2 ∨ a = -2 := by
        have h19 : a  ^ 2 = 4 := h15
        have : a = 2 ∨ a = -2 := by
          have h20 : a ^ 2 - 4 = 0 := by
            nlinarith
          have h21 : (a - 2) * (a + 2) = 0 := by
            nlinarith
          cases' (mul_eq_zero.1 h21) with h22 h23
          · -- h22 : a - 2 = 0
            left
            linarith
          · -- h23 : a + 2 = 0
            right
            linarith
        assumption
      cases h18 with
      | inl h19 =>
        right
        right
        right
        right
        exact h19
      | inr h19 =>
        left
        exact h19