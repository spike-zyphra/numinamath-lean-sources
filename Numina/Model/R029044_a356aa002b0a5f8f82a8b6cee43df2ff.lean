import Mathlib

theorem algebra_7940 (a b c : ℚ) (ha : a * b * c > 0) (hb : a + b + c < 0)
    (x : ℚ) (hx : x = |a| / a + |b| / b + |c| / c) :
    x ^ 2 - 2 * x + 3 = 6 := by
  have h1 : a ≠ 0 := by
    by_contra h
    have h2 : a * b * c = 0 := by
      rw [h]
      norm_num
    linarith
  have h2 : b ≠ 0 := by
    by_contra h
    have h3 : a * b * c = 0 := by
      rw [h]
      norm_num
    linarith
  have h3 : c ≠ 0 := by
    by_contra h
    have h4 : a * b * c = 0 := by
      rw [h]
      norm_num
    linarith
  have h4 : a > 0 ∨ a < 0 := by
    by_contra h
    push_neg at h
    have h5 : a = 0 := by
      linarith
    contradiction
  have h5 : b > 0 ∨ b < 0 := by
    by_contra h
    push_neg at h
    have h6 : b = 0 := by
      linarith
    contradiction
  have h6 : c > 0 ∨ c < 0 := by
    by_contra h
    push_neg at h
    have h7 : c = 0 := by
      linarith
    contradiction
  rcases h4 with ha_pos | ha_neg
  · -- Assume a > 0
    rcases h5 with hb_pos | hb_neg
    · -- Assume b > 0
      rcases h6 with hc_pos | hc_neg
      · -- Assume c > 0
        -- All three positive, contradicts a + b + c < 0
        exfalso
        have h7 : a + b + c > 0 := by
          linarith
        linarith
      · -- Assume c < 0
        have h8 : a * b * c < 0 := by
          have h9 : a * b > 0 := by
            apply mul_pos
            all_goals linarith
          have h10 : c < 0 := hc_neg
          nlinarith
        linarith
    · -- Assume b < 0
      rcases h6 with hc_pos | hc_neg
      · -- Assume c > 0
        -- This is a possible case
        have h7 : a * b * c < (0 : ℚ) := by
          have h8 : a * c > 0 := by
            apply mul_pos
            all_goals linarith
          have h9 : b < 0 := by linarith
          nlinarith
        linarith
      · -- Assume c < 0
        have ha1 : |a| = a := abs_of_pos ha_pos
        have hb1 : |b| = -b := abs_of_neg hb_neg
        have hc1 : |c| = -c := abs_of_neg hc_neg
        have ha2 : |a| / a = 1 := by
          rw [ha1]
          have ha3 : a ≠ 0 := h1
          field_simp [ha3]
        have hb2 : |b| / b = -1 := by
          rw [hb1]
          have hb3 : b ≠ 0 := h2
          field_simp [hb3]
        have hc2 : |c| / c = -1 := by
          rw [hc1]
          have hc3 : c ≠ 0 := h3
          field_simp [hc3]
        have hx2 : x = -1 := by
          rw [hx]
          rw [ha2, hb2, hc2]
          all_goals norm_num
        rw [hx2]
        norm_num
  · -- Assume a < 0
    rcases h5 with hb_pos | hb_neg
    · -- Assume b > 0
      rcases h6 with hc_pos | hc_neg
      · -- Assume c > 0
        have h8 : a * b * c < 0 := by
          have h9 : b * c > 0 := by
            apply mul_pos
            all_goals linarith
          have h10 : a < 0 := ha_neg
          nlinarith
        linarith
      · -- Assume c < 0
        have ha1 : |a| = -a := abs_of_neg ha_neg
        have hb1 : |b| = b := abs_of_pos hb_pos
        have hc1 : |c| = -c := abs_of_neg hc_neg
        have ha2 : |a| / a = -1 := by
          rw [ha1]
          have ha3 : a ≠ 0 := h1
          field_simp [ha3]
        have hb2 : |b| / b = 1 := by
          rw [hb1]
          have hb3 : b ≠ 0 := h2
          field_simp [hb3]
        have hc2 : |c| / c = -1 := by
          rw [hc1]
          have hc3 : c ≠ 0 := h3
          field_simp [hc3]
        have hx2 : x = -1 := by
          rw [hx]
          rw [ha2, hb2, hc2]
          all_goals norm_num
        rw [hx2]
        norm_num
    · -- Assume b < 0
      rcases h6 with hc_pos | hc_neg
      · -- Assume c > 0
        have ha1 : |a| = -a := abs_of_neg ha_neg
        have hb1 : |b| = -b := abs_of_neg hb_neg
        have hc1 : |c| = c := abs_of_pos hc_pos
        have ha2 : |a| / a = -1 := by
          rw [ha1]
          have ha3 : a ≠ 0 := h1
          field_simp [ha3]
        have hb2 : |b| / b = -1 := by
          rw [hb1]
          have hb3 : b ≠ 0 := h2
          field_simp [hb3]
        have hc2 : |c| / c = 1 := by
          rw [hc1]
          have hc3 : c ≠ 0 := h3
          field_simp [hc3]
        have hx2 : x = -1 := by
          rw [hx]
          rw [ha2, hb2, hc2]
          all_goals norm_num
        rw [hx2]
        norm_num
      · -- Assume c < 0
        have h8 : a * b * c < 0 := by
          have h9 : a * b > 0 := by
            apply mul_pos_of_neg_of_neg
            all_goals linarith
          have h10 : c < 0 := hc_neg
          nlinarith
        linarith