import Mathlib

theorem number_theory_159039 (a b c : ℤ) (h : abs (a + b + c) + 2 = abs a + abs b + abs c) :
    a^2 = 1 ∨ b^2 = 1 ∨ c^2 = 1 := by

  by_contra h1
  push_neg at h1

  have h2 : a^2 ≠ 1 := h1.1
  have h3 : b^2 ≠ 1 := h1.2.1
  have h4 : c^2 ≠ 1 := h1.2.2

  have h5 : a ≠ 1 := by
    by_contra h_eq
    rw [h_eq] at h2
    norm_num at h2

  have h6 : a ≠ -1 := by
    by_contra h_eq
    rw [h_eq] at h2
    norm_num at h2

  have h7 : b ≠ 1 := by
    by_contra h_eq
    rw [h_eq] at h3
    norm_num at h3

  have h8 : b ≠ -1 := by
    by_contra h_eq
    rw [h_eq] at h3
    norm_num at h3

  have h9 : c ≠ 1 := by
    by_contra h_eq
    rw [h_eq] at h4
    norm_num at h4

  have h10 : c ≠ -1 := by
    by_contra h_eq
    rw [h_eq] at h4
    norm_num at h4

  by_cases h11 : a ≥ 0
  · -- Case a ≥ 0
    have ha1 : abs a = a := by
      rw [abs_of_nonneg h11]
    by_cases h12 : b ≥ 0
    · -- Case b ≥ 0
      have hb1 : abs b = b := by
        rw [abs_of_nonneg h12]
      by_cases h13 : c ≥ 0
      · -- Case c ≥ 0
        have hc1 : abs c = c := by
          rw [abs_of_nonneg h13]
        have habc1 : abs (a + b + c) = a + b + c := by
          rw [abs_of_nonneg]
          all_goals linarith
        rw [ha1, hb1, hc1, habc1] at h
        all_goals omega
      · -- Case c < 0
        have hc1 : abs c = -c := by
          rw [abs_of_neg]
          linarith
        by_cases h14 : a + b + c ≥ 0
        · -- Case a + b + c ≥ 0
          have habc1 : abs (a + b + c) = a + b + c := by
            rw [abs_of_nonneg h14]
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
        · -- Case a + b + c < 0
          have habc1 : abs (a + b + c) = -(a + b + c) := by
            rw [abs_of_neg]
            linarith
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
    · -- Case b < 0
      have hb1 : abs b = -b := by
        rw [abs_of_neg]
        linarith
      by_cases h13 : c ≥ 0
      · -- Case c ≥ 0
        have hc1 : abs c = c := by
          rw [abs_of_nonneg h13]
        by_cases h14 : a + b + c ≥ 0
        · -- Case a + b + c ≥ 0
          have habc1 : abs (a + b + c) = a + b + c := by
            rw [abs_of_nonneg h14]
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
        · --  Case a + b + c < 0
          have habc1 : abs (a + b + c) = -(a + b + c) := by
            rw [abs_of_neg]
            linarith
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
      · --  Case c < 0
        have hc1 : abs c = -c := by
          rw [abs_of_neg]
          linarith
        by_cases h14 : a + b + c ≥ 0
        · --  Case a + b + c ≥ 0
          have habc1 : abs (a + b + c) = a + b + c := by
            rw [abs_of_nonneg h14]
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
        · --  Case a + b + c < 0
          have habc1 : abs (a + b + c) = -(a + b + c) := by
            rw [abs_of_neg]
            linarith
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
  · -- Case a < 0
    have ha1 : abs a = -a := by
      rw [abs_of_neg]
      linarith
    by_cases h12 : b ≥ 0
    · -- Case b ≥ 0
      have hb1 : abs b = b := by
        rw [abs_of_nonneg h12]
      by_cases h13 : c ≥ 0
      · -- Case c ≥ 0
        have hc1 : abs c = c := by
          rw [abs_of_nonneg h13]
        by_cases h14 : a + b + c ≥ 0
        · -- Case a + b + c ≥ 0
          have habc1 : abs (a + b + c) = a + b + c := by
            rw [abs_of_nonneg h14]
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
        · --  Case a + b + c < 0
          have habc1 : abs (a + b + c) = -(a + b + c) := by
            rw [abs_of_neg]
            linarith
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
      · --  Case c < 0
        have hc1 : abs c = -c := by
          rw [abs_of_neg]
          linarith
        by_cases h14 : a + b + c ≥ 0
        · --  Case a + b + c ≥ 0
          have habc1 : abs (a + b + c) = a + b + c := by
            rw [abs_of_nonneg h14]
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
        · --  Case a + b + c < 0
          have habc1 : abs (a + b + c) = -(a + b + c) := by
            rw [abs_of_neg]
            linarith
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
    · -- Case b < 0
      have hb1 : abs b = -b := by
        rw [abs_of_neg]
        linarith
      by_cases h13 : c ≥ 0
      · -- 111 Case c ≥ 0
        have hc1 : abs c = c := by
          rw [abs_of_nonneg h13]
        by_cases h14 : a + b + c ≥ 0
        · -- 111 Case a + b + c ≥ 0
          have habc1 : abs (a + b + c) = a + b + c := by
            rw [abs_of_nonneg h14]
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
        · -- 111 Case a + b + c < 0
          have habc1 : abs (a + b + c) = -(a + b + c) := by
            rw [abs_of_neg]
            linarith
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
      · -- 111 Case c < 0
        have hc1 : abs c = -c := by
          rw [abs_of_neg]
          linarith
        by_cases h14 : a + b + c ≥ 0
        · -- 11111 Case a + b + c ≥ 0
          have habc1 : abs (a + b + c) = a + b + c := by
            rw [abs_of_nonneg h14]
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega
        · -- 11111 Case a + b + c < 0
          have habc1 : abs (a + b + c) = -(a + b + c) := by
            rw [abs_of_neg]
            linarith
          rw [ha1, hb1, hc1, habc1] at h
          all_goals omega