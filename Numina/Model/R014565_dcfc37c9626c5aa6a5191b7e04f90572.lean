import Mathlib

theorem inequalities_599577 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 4) :
    1 / (11 + a ^ 2) + 1 / (11 + b ^ 2) + 1 / (11 + c ^ 2) + 1 / (11 + d ^ 2) ≤ 1 / 3 := by
  have h2 : ∀ x : ℝ, 0 < x → x ≤ 4 → 1 / (11 + x ^ 2) ≤ (1 / 12) - (1 / 72) * (x - 1) := by
    intro x hx hx2
    have h10 : 1 / (11 + x ^ 2) - ((1 / 12) - (1 / 72) * (x - 1)) ≤ 0 := by
      have h5 : 0 < (11 + x ^ 2 : ℝ) := by 
        nlinarith [sq_pos_of_pos hx]
      have h7 : 1 / (11 + x ^ 2) - ((1 / 12) - (1 / 72) * (x - 1)) =
          (72 - 6 * (11 + x ^ 2) + (11 + x ^ 2) * (x - 1)) / (72 * (11 + x ^ 2)) := by
        field_simp
        ring
      rw [h7]
      have h11 : x ≤ (4 : ℝ) := by
        linarith 
      have hk1 : (72 - 6 * (11 + x ^ 2) + (11 + x ^ 2) * (x - 1)) ≤ 0 := by 
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (x - 4), mul_pos hx (show (0 : ℝ) < 1 by linarith), sq_nonneg (x ^ 2 - 1)]
      have hk2 : (72 * (11 + x ^ 2) ) > 0 := by 
        nlinarith [sq_pos_of_pos hx, sq_nonneg (x ^ 2)]
      apply div_nonpos_of_nonpos_of_nonneg 
      linarith
      all_goals linarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 1)]
    linarith 
  have ha1 : 1 / (11 + a^2) ≤ (1 / 12) - (1 / 72) * (a - 1) := by
    apply h2 a ha (by nlinarith [h, ha, hb, hc, hd])
  have hb1 : 1 / (11 + b^2) ≤ (1 / 12) - (1 / 72) * (b - 1) := by
    apply h2 b hb (by nlinarith [h, ha, hb, hc, hd])
  have hc1 : 1 / (11 + c^2) ≤ (1 / 12) - (1 / 72) * (c - 1) := by
    apply h2 c hc (by nlinarith [h, ha, hb, hc, hd])
  have hd1 : 1 / (11 + d^2) ≤ (1 / 12) - (1 / 72) * (d - 1) := by
    apply h2 d hd (by nlinarith [h, ha, hb, hc, hd])
  have h2 : 1 / (11 + a^2) + 1 / (11 + b^2) + 1 / (11 + c^2) + 1 / (11 + d^2) ≤ 4 * (1 / 12) - (1 / 72) * (a + b + c + d - 4) := by 
    linarith [ha1, hb1, hc1, hd1]
  have h3 : 4 * (1 / 12 : ℝ) - (1 / 72) * (a + b + c + d - 4) = (1 / 3 : ℝ) := by
    rw [show a + b + c + d = (4 : ℝ) by linarith]
    norm_num 
  linarith [h2, h3]