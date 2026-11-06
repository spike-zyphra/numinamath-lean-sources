import Mathlib

theorem algebra_881 {a b c : ℝ} (ha : a ≠ 0) (h : 14 * (a^2 + b^2 + c^2) = (a + 2 * b + 3 * c)^2) :
    a / b = 1 / 2 ∧ b / c = 2 / 3 := by 
  have h10 : 10 * (b - (2 * a + 6 * c) / 10) ^ 2 + (7 / 5) * (3 * a - c) ^ 2 = 0 := by
    nlinarith 
  have h2 : (3 * a - c) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (b - (2 * a + 6 * c) / 10), sq_nonneg (3 * a - c)]
  have h3 : 3 * a - c = 0 := by 
    nlinarith [sq_nonneg (3 * a - c), h2]
  have h6 : c = 3 * a := by
    linarith 
  have h7 : 10 * (b - (2 * a + 6 * c) / 10) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (3 * a - c), sq_nonneg (b - (2 * a + 6 * c) / 10)]
  have h8 : b - (2 * a + 6 * c) / 10 = 0 := by 
    nlinarith [sq_nonneg (b - (2 * a + 6 * c) / 10), h7]
  have h9 : b = (2 * a + 6 * c) / 10 := by 
    linarith 
  have h10 : b = 2 * a := by 
    rw [show c = 3 * a by linarith [h6]] at h9
    linarith 
  have hb : b ≠ 0 := by 
    intro h0
    have ha0 : a = 0 := by 
      linarith [h10, h0] 
    tauto 
  have hc : c ≠ 0 := by 
    intro h0
    have ha0 : a = 0 := by 
      nlinarith [h6, h0] 
    tauto 
  constructor 
  · -- Show that a / b = 1 / 2 
    have hb2 : b ≠ 0 := hb 
    field_simp [hb2] 
    all_goals 
      nlinarith [h10] 
  · -- Show that b / c = 2 / 3 
    have hc2 : c ≠ 0 := hc 
    field_simp [hc2] 
    all_goals 
      nlinarith [h10, h6]