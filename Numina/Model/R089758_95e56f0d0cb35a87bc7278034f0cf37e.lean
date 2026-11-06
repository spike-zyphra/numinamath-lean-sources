import Mathlib

theorem algebra_56405 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hroots : a^2 + 2020 * a + c = 0 ∧ b^2 + 2020 * b + c = 0)
    (hprop : a / b + b / a = 98) : Real.sqrt c = 202 := by
  rcases hroots with ⟨ha2, hb2⟩
  have h1 : a * b ≠ 0 := by
    apply mul_ne_zero
    exact ha
    exact hb
  have h_eq2 : a^2 + b^2 = 98 * (a * b) := by
    have h_eq3 : a / b + b / a = 98 := hprop
    field_simp [hb, ha] at h_eq3
    nlinarith
  have h_eq3 : a^2 + 2020 * a + c - (b^2 + 2020 * b + c) = 0 := by
    linarith [ha2, hb2]
  have h_eq4 : (a - b) * (a + b + 2020) = 0 := by
    ring_nf at h_eq3 ⊢
    linarith
  cases' (mul_eq_zero.mp h_eq4) with h_eq5 h_eq6
  · -- Case where a = b, which would imply a/b + b/a = 2, contradicting the given value.
    exfalso
    have hab : a = b := by linarith
    rw [show a = b by linarith] at hprop
    field_simp [hb] at hprop
    all_goals nlinarith
  · -- Case where a + b = -2020, which we use with the earlier equation to compute ab.
    have hab : a + b = -2020 := by linarith
    have hab2 : a * b = (202 : ℝ) ^ 2 := by
      have h_eq3 : a^2 + b^2 = 98 * (a * b) := h_eq2
      have h_eq6 : (a + b) ^ 2 = 2020 ^ 2 := by
        rw [show a + b = -2020 by linarith]
        all_goals nlinarith
      nlinarith [sq_pos_of_ne_zero (show a * b ≠ 0 by assumption), h_eq6, h_eq3]
    have hc : c = a * b := by
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), hab]
    rw [hc]
    rw [hab2]
    have h_pos : (202 : ℝ) ^ 2 ≥ 0 := by positivity
    rw [Real.sqrt_sq (by norm_num)]
    all_goals nlinarith