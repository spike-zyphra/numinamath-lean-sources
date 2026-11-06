import Mathlib

theorem algebra_165676 (x : ℝ) (hx : x ≠ -1 ∧ x ≠ 1) :
    20 * (x - 2) ^ 2 / (x + 1) ^ 2 - 5 * (x + 2) ^ 2 / (x - 1) ^ 2 +
    48 * (x ^ 2 - 4) / (x ^ 2 - 1) = 0 ↔ x = 2 / 3 ∨ x = 3 := by
  constructor
  · -- Forward direction: if the equation holds, then prove x = 2/3 ∨ x = 3
    intro h_eq
    have h1 : x + 1 ≠ 0 := by
      intro h
      apply hx.1
      linarith
    have h2 : x - 1 ≠ 0 := by
      intro h
      apply hx.2
      linarith
    have eq1 : 20 * (x - 2) ^ 2 * (x - 1) ^ 2 - 5 * (x + 2) ^ 2 * (x + 1) ^ 2 + 48 * (x ^ 2 - 4) * (x + 1) * (x - 1) = 0 := by
      have eq2 : 20 * (x - 2) ^ 2 / (x + 1) ^ 2 - 5 * (x + 2) ^ 2 / (x - 1) ^ 2 + 48 * (x ^ 2 - 4) / (x ^ 2 - 1) =
          (20 * (x - 2) ^ 2 * (x - 1) ^ 2 - 5 * (x + 2) ^ 2 * (x + 1) ^ 2 + 48 * (x ^ 2 - 4) * (x + 1) * (x - 1)) / ((x + 1) ^ 2 * (x - 1) ^ 2) := by
        field_simp [(show x + 1 ≠ 0 by exact h1), (show x - 1 ≠ 0 by exact h2), (show x ^ 2 - 1 ≠ 0 by
          have h3 : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
          rw [h3]
          apply mul_ne_zero
          · exact h2
          · exact h1
        )]
        ring
      rw [eq2] at h_eq
      have eq3 : (20 * (x - 2) ^ 2 * (x - 1) ^ 2 - 5 * (x + 2) ^ 2 * (x + 1) ^ 2 + 48 * (x ^ 2 - 4) * (x + 1) * (x - 1)) / ((x + 1) ^ 2 * (x - 1) ^ 2) = 0 := h_eq
      have eq4 : 20 * (x - 2) ^ 2 * (x - 1) ^ 2 - 5 * (x + 2) ^ 2 * (x + 1) ^ 2 + 48 * (x ^ 2 - 4) * (x + 1) * (x - 1) = 0 := by
        field_simp [(show (x + 1) ^ 2 * (x - 1) ^ 2 ≠ 0 by
          have h1' : x + 1 ≠ 0 := h1
          have h2' : x - 1 ≠ 0 := h2
          simp [h1', h2']
        )] at eq3 ⊢
        linarith
      linarith
    have eq2 : (x - 2 / 3) * (x - 3) = 0 := by
      nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (x - 3), sq_pos_of_ne_zero (show (x + 1 : ℝ) ≠ 0 by exact h1), sq_pos_of_ne_zero (show (x - 1 : ℝ) ≠ 0 by exact h2), sq_nonneg (x ^ 2 - 1)]
    cases' (mul_eq_zero.1 eq2) with h3 h4
    · -- x - 2/3 = 0
      left
      linarith
    · -- x - 3 = 0
      right
      linarith
  · -- Backward direction: if x = 2/3 ∨ x = 3, then the equation holds
    rintro (h | h)
    · -- x = 2/3
      rw [h]
      norm_num
    · -- x = 3
      rw [h]
      norm_num