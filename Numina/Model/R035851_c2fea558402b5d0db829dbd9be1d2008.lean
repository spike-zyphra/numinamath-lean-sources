import Mathlib

theorem algebra_3430 {x1 x2 k : ℝ} (hx1 : x1^2 - 8 * x1 + k = 0) (hx2 : x2^2 - 8 * x2 + k = 0)
    (hroots : x1 ≠ x2) (hsum : 1 / x1 + 1 / x2 = 2 / 3) : k = 12 := by

  have h1 : x1 - x2 ≠ 0 := by
    intro h
    apply hroots
    linarith

  have h6 : x1 + x2 = 8 := by
    have eq1 : (x1 - x2) * (x1 + x2 - 8) = 0 := by
      nlinarith [hx1, hx2]
    cases' (mul_eq_zero.1 eq1) with h7 h8
    · -- x1 - x2 = 0, which is a contradiction
      exfalso
      apply hroots
      linarith
    · -- x1 + x2 -8 =0
      linarith

  have h7 : x1 * x2 = k := by
    nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by exact h1), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 - 8)]

  have h81 : x1 ≠ 0 := by
    by_contra h
    have h10 : x1 = 0 := by
      linarith
    have hk1 : k = 0 := by
      rw [h10] at hx1
      nlinarith
    have h4 : x2 = 8 := by
      linarith [h6, h10]
    rw [h10, h4] at hsum
    field_simp at hsum
    all_goals linarith [hk1, h4]

  have h82 : x2 ≠ 0 := by
    by_contra h
    have h10 : x2 = 0 := by
      linarith
    have hk2 : k = 0 := by
      rw [h10] at hx2
      nlinarith
    have h5 : x1 = 8 := by
      linarith [h6, h10]
    rw [h5, h10] at hsum
    field_simp at hsum
    all_goals linarith [hk2, h5]

  have eq1 : x1 + x2 = 2 * (x1 * x2) / 3 := by
    field_simp [h81, h82] at hsum ⊢
    linarith

  rw [h6, h7] at eq1
  nlinarith