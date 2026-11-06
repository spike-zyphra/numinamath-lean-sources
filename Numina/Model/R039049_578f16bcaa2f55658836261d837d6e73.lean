import Mathlib

theorem algebra_190156 (x : ℝ) (hx : x ≠ 49 ∧ x ≠ 50) :
    (x - 49) / 50 + (x - 50) / 49 = 49 / (x - 50) + 50 / (x - 49) ↔
    x = 0 ∨ x = 99 ∨ x = 4901 / 99 := by
  rcases hx with ⟨hx49, hx50⟩
  constructor
  · -- Assume the equation holds, prove x = 0 ∨ x = 99 ∨ x = 4901 / 99
    intro h_eq
    have hx49' : x - 49 ≠ 0 := by
      intro h
      apply hx49
      linarith
    have hx50' : x - 50 ≠ 0 := by
      intro h
      apply hx50
      linarith
    field_simp [hx49', hx50'] at h_eq
    have h_eq2 : (x - 0) * (x - 99) * (x - 4901 / 99) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (50 : ℝ) ≠ 0 by norm_num), sq_pos_of_ne_zero (show (49 : ℝ) ≠ 0 by norm_num), sq_pos_of_ne_zero (show (x - 49 : ℝ) ≠ 0 by intro h; apply hx49; linarith), sq_pos_of_ne_zero (show (x - 50 : ℝ) ≠ 0 by intro h; apply hx50; linarith), sq_nonneg (x - 0), sq_nonneg (x - 99), sq_nonneg (x - 4901 / 99)]
    cases' (mul_eq_zero.mp h_eq2) with h1 h2
    cases' (mul_eq_zero.mp h1) with h0 h99
    · -- x - 0 = 0
      left
      linarith
    · -- x - 99 = 0
      right
      left
      linarith
    · -- x - 4901 / 99 = 0
      right
      right
      linarith
  · -- Assume x = 0 ∨ x = 99 ∨ x = 4901 / 99, prove the equation
    rintro (h | h | h)
    · -- x = 0
      rw [h]
      norm_num
    · -- x = 99
      rw [h]
      norm_num
    · -- x = 4901 / 99
      rw [h]
      norm_num