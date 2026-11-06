import Mathlib

theorem number_theory_295137 {a b : ℕ} (ha : 0 < a) (hb : b < a)
    (h : (2 ^ 8060 - 1) / ((2 ^ 4030 + 1) * (2 ^ 2015 - 1)) = 2 ^ a + b) :
    a + b = 2016 := by

  have h1 : (2 ^ 8060 - 1) / ((2 ^ 4030 + 1) * (2 ^ 2015 - 1)) = 2 ^ 2015 + 1 := by
    norm_num
    <;> ring_nf <;> omega

  rw [h1] at h

  have h2 : a ≤ 2015 := by
    by_contra h2
    push_neg at h2
    have h3 : 2 ^ a + b ≥ 2 ^ 2016 := by
      have h4 : a ≥ 2016 := by
        omega
      have h5 : 2 ^ a ≥ 2 ^ 2016 := by
        have h6 : a ≥ 2016 := h4
        have h7 : 2 ^ a ≥ 2 ^ 2016 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        linarith
      have h8 : b ≥ 1 := by
        omega
      omega
    have h8 : 2 ^ 2015 + 1 ≥ 2 ^ 2016 := by
      omega
    have h9 : False := by
      have h10 : 2 ^ 2015 + 1 < 2 ^ 2016 := by
        have h11 : 2 ^ 2015 < 2 ^ 2016 := by
          omega
        omega
      omega
    linarith

  have h3 : a ≥ 2015 := by
    by_contra h3
    push_neg at h3
    have h4 : a ≤ 2014 := by
      omega
    have h5 : 2 ^ a ≤ 2 ^ 2014 := by
      have h6 : a ≤ 2014 := h4
      have h7 : 2 ^ a ≤ 2 ^ 2014 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals omega
      linarith
    have h6 : b ≤ 2014 := by
      have h7 : 2 ^ a + b ≤ 2 ^ 2014 + 2014 := by
        have h8 : b ≤ 2014 := by
          omega
        have h9 : 2 ^ a ≤ 2 ^ 2014 := h5
        omega
      have h8 : 2 ^ 2015 + 1 ≤ 2 ^ 2014 + 2014 := by
        omega
      norm_num at h8
      all_goals omega
    have h7 : a ≤ 2014 := h4
    -- Derive a contradiction
    omega

  have h4 : a = 2015 := by
    omega

  have h5 : b = 1 := by
    rw [h4] at h
    have h6 : 2 ^ 2015 + 1 = 2 ^ 2015 + b := by
      omega
    omega

  omega