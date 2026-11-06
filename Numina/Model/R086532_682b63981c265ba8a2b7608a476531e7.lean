import Mathlib

theorem algebra_175348 (x : ℝ) (hx : x ≠ 3) :
    x - 7 = 4 * abs (x - 3) / (x - 3) ↔ x = 11 := by
  constructor
  · -- Forward implication: prove that if the equation holds, then x = 11
    intro h
    have h1 : (x - 3) ≠ 0 := by
      intro h2
      apply hx
      linarith
    have h_eq : (x - 7) * (x - 3) = 4 * abs (x - 3) := by
      have h2 : (x - 3) ≠ 0 := h1
      field_simp [h2] at h ⊢
      linarith [h]
    by_cases h2 : (x - 3) ≥ 0
    · -- In this case, abs (x - 3) = x - 3
      have h_abs : abs (x - 3) = x - 3 := by
        rw [abs_of_nonneg]
        linarith
      rw [h_abs] at h_eq
      have : (x - 11) * (x - 3) = 0 := by
        nlinarith [h_eq]
      cases' (mul_eq_zero.1 this) with h_a h_b
      · -- h_a: x - 11 = 0
        linarith
      · -- h_b: x - 3 = 0
        exfalso
        apply h1
        linarith
    · -- Case where (x - 3) < 0, abs (x - 3) = 3 - x
      have h3 : (x - 3) < 0 := by
        by_contra h4
        push_neg at h4
        have : (x - 3) ≥ 0 := by linarith
        linarith [h2, this]
      have h_abs : abs (x - 3) = 3 - x := by
        rw [abs_of_neg]
        linarith
        all_goals linarith
      rw [h_abs] at h_eq
      have h_eq2 : (x - 3) ^ 2 = 0 := by
        nlinarith
      have h_zero : (x - 3) = 0 := by
        apply pow_eq_zero
        exact h_eq2
      exfalso
      apply h1
      linarith
  · -- Backward implication: prove that x = 11 satisfies the equation
    intro h_eq
    rw [h_eq]
    norm_num [abs_of_pos]
    all_goals norm_num