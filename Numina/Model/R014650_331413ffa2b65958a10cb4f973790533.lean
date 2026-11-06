import Mathlib

theorem algebra_251883 {x : ℝ} (hx : x ≠ 1) :
    abs (x / (x - 1)) + abs x = x ^ 2 / abs (x - 1) ↔ x = 0 ∨ x > 1 := by
  constructor
  · -- Assume abs (x / (x - 1)) + abs x = x ^ 2 / abs (x - 1) prove x = 0 ∨ x > 1
    intro h_eq
    by_cases h1 : x > 1
    · -- If x > 1, then clearly x > 1 holds
      right
      exact h1
    by_cases h2 : x ≥ 0
    · -- Case x ≥ 0 and not > 1, which means 0 ≤ x ≤ 1
      by_cases h3 : x < 1
      · -- Case 0 ≤ x < 1
        have h4 : abs x = x := abs_of_nonneg (show 0 ≤ x by linarith)
        have h5 : abs (x / (x - 1)) = - (x / (x - 1)) := by
          rw [abs_of_nonpos]
          · -- Show that x / (x - 1) ≤ 0
            have h3' : x - 1 < 0 := by nlinarith
            have hx1_nonneg : x ≥ 0 := by linarith
            have h7 : x / (x - 1) ≤ 0 := by
              apply div_nonpos_of_nonneg_of_nonpos
              · linarith
              · linarith
            linarith
          all_goals linarith
        have h6 : abs (x - 1) = 1 - x := by
          rw [abs_of_neg]
          all_goals nlinarith
        rw [h4, h5, h6] at h_eq
        have h_eq3 : 2 * x * (1 - x) = 0 := by
          field_simp [(show x - 1 ≠ 0 by intro h; apply hx; linarith), (show (1 - x) ≠ 0 by nlinarith)] at h_eq ⊢
          nlinarith [sq_nonneg (x - 1), sq_nonneg x, sq_nonneg (x - 0)]
        cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
        · -- Case 2 * x = 0, so x = 0
          left
          linarith
        · -- Case 1 - x = 0, so x = 1, which is excluded by assumption
          exfalso
          have hx1 : x = 1 := by linarith
          tauto
      · -- Case x ≥ 1, which with ¬(x > 1) means x = 1, which is excluded
        have h3' : x = 1 := by nlinarith
        exfalso
        tauto
    · -- Case x < 0
      have h4 : abs x = -x := abs_of_nonpos (show x ≤ 0 by linarith)
      have h5 : abs (x / (x - 1)) = x / (x - 1) := by
        have h8 : x / (x - 1) ≥ 0 := by
          apply div_nonneg_of_nonpos
          all_goals
            nlinarith
        rw [abs_of_nonneg h8]
      have h6 : abs (x - 1) = 1 - x := by
        rw [abs_of_neg]
        all_goals nlinarith
      rw [h4, h5, h6] at h_eq
      exfalso
      field_simp [(show x - 1 ≠ 0 by intro h; apply hx; linarith), (show (1 - x) ≠ 0 by nlinarith)] at h_eq ⊢
      nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by nlinarith), sq_nonneg (x - 0)]
  · -- Assume x = 0 ∨ x > 1 prove abs (x / (x - 1)) + abs x = x ^ 2 / abs (x - 1)
    rintro (h | h)
    · -- Case x = 0
      rw [h]
      norm_num [abs_of_nonneg, abs_of_nonpos, abs_of_pos, abs_of_neg, div_eq_mul_inv]
    · -- Case x > 1
      have h1 : x > 1 := h
      have h2 : abs x = x := abs_of_nonneg (show 0 ≤ x by linarith)
      have h3 : abs (x / (x - 1)) = x / (x - 1) := by
        have h8 : x / (x - 1) ≥ 0 := by
          apply div_nonneg
          all_goals
            nlinarith
        rw [abs_of_nonneg h8]
      have h4 : abs (x - 1) = x - 1 := by
        rw [abs_of_pos]
        nlinarith
      rw [h2, h3, h4]
      field_simp [(show x - 1 ≠ 0 by intro h; apply hx; linarith)]
      <;> nlinarith