import Mathlib

open Real

theorem inequalities_189601 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b > c) (h2 : a + c > b) (h3 : b + c > a) (h4 : c = 5 * (a + b) / 9) :
    16 / 81 ≤ (4 * (a + b) ^ 2) / (81 * a * b) ∧
    (4 * (a + b) ^ 2) / (81 * a * b) < 2 / 7 := by

  have h5 : 0 < a * b := mul_pos ha hb

  have h10 : 16 / 81 ≤ (4 * (a + b) ^ 2) / (81 * a * b) := by
    have h6 : 0 < 81 * a * b := by positivity
    suffices 16 / 81 * (81 * a * b) ≤ (4 * (a + b) ^ 2) / (81 * a * b) * (81 * a * b) by
      apply (mul_le_mul_right h6).mp
      linarith
    field_simp at *
    nlinarith [sq_nonneg (a - b)]
  
  have h13 : (4 * (a + b) ^ 2) / (81 * a * b) < 2 / 7 := by
    have h14 : 0 < 81 * a * b := by positivity
    have h15 : 0 < a + b := by linarith [ha, hb]
    have h16 : 0 < a + b := by linarith [ha, hb]
    rw [h4] at h1 h2 h3
    have h_ineq1 : 14 * a > 4 * b := by linarith [h1, h2, h3]
    have h_ineq2 : 14 * b > 4 * a := by linarith [h1, h2, h3]
    have h18 : (a + b) ^ 2 < (81 / 14) * (a * b) := by
      nlinarith [mul_pos ha hb, sq_pos_of_pos h16]
    have h19 : 4 * (a + b) ^ 2 < (81 / 14) * (a * b) * 4 := by
      linarith [h18]
    have h20 : (4 * (a + b) ^ 2) / (81 * a * b) < 2 / 7 := by
      have pos1 : 0 < 81 * a * b := by positivity
      have pos2 : 0 < 4 * (a + b) ^ 2 := by positivity
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith
  
  exact ⟨h10, h13⟩