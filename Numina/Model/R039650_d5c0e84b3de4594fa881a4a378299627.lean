import Mathlib

theorem inequalities_5810 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 3) (habc : a * b * c ≠ 0) :
    5 * (1 / a + 1 / b + 1 / c) ≤ 12 / (a * b * c) + 3 := by

  have ha1 : a ≠ 0 := by
    by_contra h1
    have : a * b * c = 0 := by
      rw [h1]
      norm_num
    contradiction

  have hb1 : b ≠ 0 := by
    by_contra h1
    have : a * b * c = 0 := by
      rw [h1]
      norm_num
    contradiction

  have hc1 : c ≠ 0 := by
    by_contra h1
    have : a * b * c = 0 := by
      rw [h1]
      norm_num
    contradiction

  have h2 : a * b * c > 0 := by
    have ha2 : a > 0 := by
      by_contra h3
      push_neg at h3
      have ha0 : a = 0 := by linarith
      rw [ha0] at habc
      simp at habc
    have hb2 : b > 0 := by
      by_contra h3
      push_neg at h3
      have hb0 : b = 0 := by linarith
      rw [hb0] at habc
      simp at habc
    have hc2 : c > 0 := by
      by_contra h3
      push_neg at h3
      have hc0 : c = 0 := by linarith
      rw [hc0] at habc
      simp at habc
    have h3 : a * b * c > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    linarith

  have h3 : 5 * (a * b + a * c + b * c) ≤ 12 + 3 * (a * b * c) := by
    have h4 : a + b + c = 3 := h
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  h, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
                  mul_pos (show 0 < a by positivity) (show 0 < b by positivity), 
                  mul_pos (show 0 < b by positivity) (show 0 < c by positivity), 
                  mul_pos (show 0 < a by positivity) (show 0 < c by positivity)
                  ]

  have h4 : 5 * (1 / a + 1 / b + 1 / c) - (12 / (a * b * c) + 3) ≤ 0 := by
    have h7 : 5 * (1 / a + 1 / b + 1 / c) - (12 / (a * b * c) + 3) = 
                (5 * (a * b + a * c + b * c) - (12 + 3 * (a * b * c))) / (a * b * c) := by
      field_simp [ha1, hb1, hc1, show a * b * c ≠ 0 by tauto]
      ring
    rw [h7]
    have h7' : 5 * (a * b + a * c + b * c) - (12 + 3 * (a * b * c)) ≤ 0 := by linarith [h3]
    have h8 : (5 * (a * b + a * c + b * c) - (12 + 3 * (a * b * c))) / (a * b * c) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      all_goals
      linarith [show 0 < a * b * c by linarith [h2]]
    linarith

  linarith