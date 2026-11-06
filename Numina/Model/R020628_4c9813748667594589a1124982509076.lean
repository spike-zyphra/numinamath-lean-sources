import Mathlib

theorem algebra_4565 {a b c : ℝ} (ha : a > 0) :
    IsLeast {y | ∃ x, y = a * x ^ 2 + b * x + c} ((4 * a * c - b ^ 2) / (4 * a)) ∧ (∀ x, a * x ^ 2 + b * x + c ≥ (4 * a * c - b ^ 2) / (4 * a) ∧ (a * x ^ 2 + b * x + c = (4 * a * c - b ^ 2) / (4 * a) ↔ x = -b / (2 * a))) := by
  constructor
  · -- Prove that (4ac - b^2)/(4a) is the minimum element in the image of the quadratic
    constructor
    · -- Show that (4ac - b^2)/(4a) is in the image
      use -b / (2 * a)
      field_simp
      <;> nlinarith [ha]
    · -- Show that (4ac - b^2)/(4a) is the minimum
      intro y hy
      rcases hy with ⟨x, hx⟩
      have h1 : a * x ^ 2 + b * x + c ≥ (4 * a * c - b ^ 2) / (4 * a) := by
        have h2 : a * x ^ 2 + b * x + c - (4 * a * c - b ^ 2) / (4 * a) ≥ 0 := by
          have h3 : a * x ^ 2 + b * x + c - (4 * a * c - b ^ 2) / (4 * a) = a * (x + b / (2 * a)) ^ 2 := by
            field_simp
            <;> ring
          rw [h3]
          have h4 : a * (x + b / (2 * a)) ^ 2 ≥ 0 := by
            apply mul_nonneg
            linarith
            apply pow_two_nonneg
          linarith
        linarith
      linarith [h1, hx]
  · -- Prove the inequality and equality condition for all x
    intro x
    constructor
    · -- Show the inequality
      have h1 : a * x ^ 2 + b * x + c ≥ (4 * a * c - b ^ 2) / (4 * a) := by
        have h2 : a * x ^ 2 + b * x + c - (4 * a * c - b ^ 2) / (4 * a) ≥ 0 := by
          have h3 : a * x ^ 2 + b * x + c - (4 * a * c - b ^ 2) / (4 * a) = a * (x + b / (2 * a)) ^ 2 := by
            field_simp
            <;> ring
          rw [h3]
          have h4 : a * (x + b / (2 * a)) ^ 2 ≥ 0 := by
            apply mul_nonneg
            linarith
            apply pow_two_nonneg
          linarith
        linarith
      linarith
    · -- Show the equality condition
      constructor
      · -- Assume equality holds, prove x = -b/(2a)
        intro heq
        have h2 : a * x ^ 2 + b * x + c = (4 * a * c - b ^ 2) / (4 * a) := by linarith [heq]
        have h3 : a * (x + b / (2 * a)) ^ 2 = 0 := by
          have eq1 : a * x ^ 2 + b * x + c - (4 * a * c - b ^ 2) / (4 * a) = 0 := by linarith
          have eq2 : a * x ^ 2 + b * x + c - (4 * a * c - b ^ 2) / (4 * a) = a * (x + b / (2 * a)) ^ 2 := by
            field_simp
            <;> ring
          rw [eq2] at eq1
          linarith
        have h4 : x = -b / (2 * a) := by
          have h5 : (x + b / (2 * a)) ^ 2 = 0 := by
            have h6 : a * (x + b / (2 * a)) ^ 2 = 0 := h3
            have h7 : (x + b / (2 * a)) ^ 2 = 0 := by
              apply (mul_left_inj' (show a ≠ 0 by linarith)).mp
              linarith
            exact h7
          have h8 : x + b / (2 * a) = 0 := by
            apply pow_eq_zero 
            exact h5
          field_simp at h8 ⊢
          <;> linarith
        exact h4
      · -- Assume x = -b/(2a), prove equality
        intro h_eq
        rw [h_eq]
        field_simp
        <;> nlinarith