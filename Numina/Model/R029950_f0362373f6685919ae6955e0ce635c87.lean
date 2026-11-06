import Mathlib

theorem inequalities_282838 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hne1a : a ≠ 1) (hne1b : b ≠ 1) :
    (a^5 - 1) / (a^4 - 1) * (b^5 - 1) / (b^4 - 1) > (25 / 64) * (a + 1) * (b + 1) := by
  have h1 : (a^5 - 1) / (a^4 - 1) > (5 / 8) * (a + 1) := by
    by_cases h15 : a > 1
    · -- Case a > 1.
      have h16 : a ^ 4 - 1 > 0 := by
        have h17 : a ^ 4 > 1 := by
          have h19 : a > 1 := by linarith
          have h20 : a ^ 2 > 1 := by nlinarith
          have h21 : a ^ 4 = (a ^ 2) ^ 2 := by ring
          nlinarith [show a ^ 2 > 0 by nlinarith]
        linarith
      have h18 : (a^5 - 1) / (a^4 - 1) > (5 / 8) * (a + 1) := by
        apply (lt_div_iff₀ (by linarith)).mpr
        nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (a ^ 2 - a), sq_nonneg (a - 1), sq_pos_of_pos ha, sq_pos_of_ne_zero (show a - 1 ≠ 0 by
          intro h
          apply hne1a
          linarith
        )
        ]
      linarith
    · -- Case 0 < a ≤ 1.
      have h17 : a ≤ 1 := by linarith
      have h18 : a < 1 := by
        by_contra h
        push_neg at h
        have h19 : a = 1 := by linarith
        tauto
      have h19 : a ^ 4 - 1 < 0 := by
        have h20 : a < 1 := by linarith
        have h21 : a ^ 4 < 1 := by
          have h22 : a < 1 := by linarith
          have h23 : a ^ 2 < 1 := by nlinarith
          have h24 : a ^ 4 = (a ^ 2) ^ 2 := by ring
          nlinarith [show a ^ 2 > 0 by nlinarith]
        linarith
      have h20 : (a^5 - 1) / (a^4 - 1) > (5 / 8) * (a + 1) := by
        apply (lt_div_iff_of_neg' (by linarith)).mpr
        nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (a ^ 2 - a), sq_nonneg (a - 1), sq_pos_of_pos ha, sq_pos_of_ne_zero (show a - 1 ≠ 0 by
          intro h
          apply hne1a
          linarith
        )
        ]
      linarith
  have h2 : (b^5 - 1) / (b^4 - 1) > (5 / 8) * (b + 1) := by
    by_cases h15 : b > 1
    · -- Case b > 1.
      have h16 : b ^ 4 - 1 > 0 := by
        have h17 : b ^ 4 > 1 := by
          have h19 : b > 1 := by linarith
          have h20 : b ^ 2 > 1 := by nlinarith
          have h21 : b ^ 4 = (b ^ 2) ^ 2 := by ring
          nlinarith [show b ^ 2 > 0 by nlinarith]
        linarith
      have h18 : (b^5 - 1) / (b^4 - 1) > (5 / 8) * (b + 1) := by
        apply (lt_div_iff₀ (by linarith)).mpr
        nlinarith [sq_nonneg (b ^ 2 - 1), sq_nonneg (b ^ 2 - b), sq_nonneg (b - 1), sq_pos_of_pos hb, sq_pos_of_ne_zero (show b - 1 ≠ 0 by
          intro h
          apply hne1b
          linarith
        )
        ]
      linarith
    · -- Case 0 < b ≤ 1.
      have h17 : b ≤ 1 := by linarith
      have h18 : b < 1 := by
        by_contra h
        push_neg at h
        have h19 : b = 1 := by linarith
        tauto
      have h19 : b ^ 4 - 1 < 0 := by
        have h20 : b < 1 := by linarith
        have h21 : b ^ 4 < 1 := by
          have h22 : b < 1 := by linarith
          have h23 : b ^ 2 < 1 := by nlinarith
          have h24 : b ^ 4 = (b ^ 2) ^ 2 := by ring
          nlinarith [show b ^ 2 > 0 by nlinarith]
        linarith
      have h20 : (b^5 - 1) / (b^4 - 1) > (5 / 8) * (b + 1) := by
        apply (lt_div_iff_of_neg' (by linarith)).mpr
        nlinarith [sq_nonneg (b ^ 2 - 1), sq_nonneg (b ^ 2 - b), sq_nonneg (b - 1), sq_pos_of_pos hb, sq_pos_of_ne_zero (show b - 1 ≠ 0 by
          intro h
          apply hne1b
          linarith
        )
        ]
      linarith
  have h3 : (a^5 - 1) / (a^4 - 1) * ((b^5 - 1) / (b^4 - 1)) > ((5 / 8) * (a + 1)) * ((5 / 8) * (b + 1)) := by
    have h4 : (a^5 - 1) / (a^4 - 1) > (5 / 8) * (a + 1) := h1
    have h5 : (b^5 - 1) / (b^4 - 1) > (5 / 8) * (b + 1) := h2
    apply mul_lt_mul_of_pos'
    all_goals
    try linarith [h4, h5]
    all_goals
    try positivity
  have h5 : ((5 / 8) * (a + 1)) * ((5 / 8) * (b + 1)) = (25 / 64) * (a + 1) * (b + 1) := by
    ring
  have h7 : (a^5 - 1) / (a^4 - 1) * (b^5 - 1) / (b^4 - 1) = (a^5 - 1) / (a^4 - 1) * ((b^5 - 1) / (b^4 - 1)) := by
    ring
  linarith [h3, h5, h7]