import Mathlib

theorem algebra_223817 {a b : ℝ} (ha : a ≠ 1) (hb : b ≠ 1)
    (h : a + b = 1) :
    a / (b^3 - 1) - b / (a^3 - 1) = (2 * b - 2 * a) / (a^2 * b^2 + 3) := by

  have h1 : b = 1 - a := by linarith
  rw [h1]
  have ha2 : a - 1 ≠ 0 := by
    intro h2
    apply ha
    linarith
  have h2 : (1 - a) ^ 3 - 1 ≠ 0 := by
    by_contra h3
    have h4 : (1 - a) = 1 := by
      have h5 : (1 - a) ^ 3 - 1 = 0 := by linarith
      have h6 : (1 - a - 1) * ((1 - a) ^ 2 + (1 - a) + 1) = 0 := by nlinarith
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- 1 - a - 1 = 0
        nlinarith
      · -- (1 - a) ^ 2 + (1 - a) + 1 = 0
        nlinarith [sq_nonneg ((1 - a) + 1 / 2), sq_nonneg ((1 - a) ^ 2)]
    have h4' : a = 0 := by linarith
    have h5 : (b : ℝ) = 1 := by
      rw [h1]
      linarith
    tauto
  have h3 : a ^ 3 - 1 ≠ 0 := by
    by_contra h4
    have h5 : a ^ 3 - 1 = 0 := by linarith
    have h6 : (a - 1) * (a ^ 2 + a + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- a - 1 = 0
      have h8 : a = 1 := by linarith
      tauto
    · -- a ^ 2 + a + 1 = 0
      nlinarith [sq_nonneg (a + 1 / 2), sq_nonneg (a ^ 2)]
  have h4 : a ^ 2 * (1 - a) ^ 2 + 3 ≠ 0 := by
    nlinarith [sq_nonneg (a * (1 - a)), sq_nonneg (a + (1 - a)), sq_nonneg (a - 1)]
  field_simp [(show (1 - a) ^ 3 - 1 ≠ 0 by assumption), (show a ^ 3 - 1 ≠ 0 by assumption), (show a ^ 2 * (1 - a) ^ 2 + 3 ≠ 0 by assumption)]
  <;> ring_nf
  <;> nlinarith [sq_pos_of_ne_zero (show a - 1 ≠ 0 by
    intro h2
    apply ha2
    linarith
  ), sq_pos_of_ne_zero (show (1 - a) - 1 ≠ 0 by
    intro h2
    have h3 : (b : ℝ) = 1 := by
      nlinarith [h1, h2]
    tauto
  )]