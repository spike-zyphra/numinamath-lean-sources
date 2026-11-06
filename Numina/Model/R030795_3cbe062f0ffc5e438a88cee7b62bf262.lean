import Mathlib

theorem algebra_323456 {a : ℝ} (ha : a ≠ 0) :
    a^3 + a^2 - 3*a + 2 = 3/a - 1/a^2 - 1/a^3 → a + 1/a = 2 ∨ a + 1/a = -3 := by
  intro h
  have h1 : a^6 + a^5 - 3*a^4 + 2*a^3 - 3*a^2 + a + 1 = 0 := by
    have h2 : a^3 + a^2 - 3*a + 2 = 3/a - 1/a^2 - 1/a^3 := h
    have h3 : a ^ 3 * (a^3 + a^2 - 3*a + 2) = a ^ 3 * (3/a - 1/a^2 - 1/a^3) := by
      rw [h2]
    have h4 : a ^ 3 * (a^3 + a^2 - 3*a + 2) = a^6 + a^5 - 3*a^4 + 2*a^3 := by
      ring
    have h5 : a ^ 3 * (3 / a - 1 / a^2 - 1 / a^3) = 3*a^2 - a - 1 := by
      field_simp [ha]
      <;> ring
    rw [h4, h5] at h3
    nlinarith
  have h2 : (a - 1)^2 * (a^2 + 1) * (a^2 + 3*a + 1) = 0 := by
    nlinarith [sq_nonneg (a^2), sq_nonneg (a - 1), sq_nonneg (a^2 - 1), sq_nonneg (a^2 + 3*a + 1), sq_pos_of_pos (show (0:ℝ) < 2 by norm_num), sq_pos_of_ne_zero ha]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · cases' (mul_eq_zero.mp h3) with h5 h6
    · -- Case $ (a - 1)^2 = 0 $
      have ha1 : a = 1 := by
        nlinarith
      left
      rw [ha1]
      norm_num
    · -- Case $a^2 + 1 = 0$
      -- This is impossible in real numbers
      have h7 : a^2 = -1 := by
        linarith
      nlinarith [sq_nonneg a]
  · -- Case $a^2 + 3*a + 1 = 0$
    right
    have h7 : a^2 + 3*a + 1 = 0 := by
      linarith [h4]
    have h8 : a + 1 / a = -3 := by
      have h9 : a ≠ 0 := ha
      field_simp at *
      nlinarith [h7, sq_pos_of_ne_zero ha]
    linarith [h8]