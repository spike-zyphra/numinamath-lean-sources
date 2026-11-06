import Mathlib

theorem algebra_599537 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (a + 2 * b + 3 * c) ^ 2 = 14 * (a ^ 2 + b ^ 2 + c ^ 2)) :
    (b + c) / a + (a + c) / b + (a + b) / c = 8 := by

  have eq1 : 13 * a^2 + 10 * b^2 + 5 * c^2 - 4 * a * b - 6 * a * c - 12 * b * c = 0 := by
    nlinarith [h]

  have h5 : 13 * (a - (2 * b + 3 * c) / 13) ^ 2 + (14 / 13) * (3 * b - 2 * c) ^ 2 = 0 := by
    nlinarith [eq1]

  have h6 : (3 * b - 2 * c) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - (2 * b + 3 * c) / 13), sq_nonneg (3 * b - 2 * c)]

  have h7 : 3 * b - 2 * c = 0 := by
    rwa [sq_eq_zero_iff] at h6

  have h8 : c = 3 / 2 * b := by
    linarith [h7]

  have h9 : a - (2 * b + 3 * c) / 13 = 0 := by
    nlinarith [sq_nonneg (a - (2 * b + 3 * c) / 13), sq_nonneg (3 * b - 2 * c)]

  have h10 : a = (2 * b + 3 * c) / 13 := by linarith [h9]

  rw [h8] at h10

  have h11 : a = b / 2 := by
    field_simp at h10 ⊢
    <;> nlinarith

  have h12 : a = b / 2 := h11
  have h13 : c = 3 / 2 * b := h8

  have h14 : (b + c) / a + (a + c) / b + (a + b) / c = 8 := by
    rw [h12, h13]
    field_simp [hb, show b ≠ 0 by exact hb] -- $b \neq 0$
    <;> nlinarith [sq_pos_of_ne_zero (show b ≠ 0 by exact hb)]

  exact h14