import Mathlib

theorem algebra_236591 {x : ℕ} (h : x^3 = 2011^2 + 2011 * 2012 + 2012^2 + 2011^3) :
    x = 2012 := by
  have h1 : x^3 = 2012^3 := by
    calc
      x^3 = 2011^2 + 2011 * 2012 + 2012^2 + 2011^3 := h
      _ = 2012^3 := by norm_num
  have h2 : x = 2012 := by
    have h3 : x^3 = 2012^3 := h1
    have h4 : x ≤ 2012 := by
      by_contra h5
      push_neg at h5
      have h5' : x > 2012 := by omega
      have h6 : x^3 > 2012^3 := by
        have h7 : x ≥ 2013 := by omega
        have h8 : x^3 ≥ 2013^3 := by
          have h9 : x ≥ 2013 := h7
          have h10 : x^3 ≥ 2013^3 := by
            apply Nat.pow_le_pow_of_le_left
            all_goals linarith
          linarith
        have h11 : 2013^3 > 2012^3 := by norm_num
        linarith
      linarith
    have h5 : x ≥ 2012 := by
      by_contra h6
      push_neg at h6
      have h6' : x < 2012 := by omega
      have h7 : x ≤ 2011 := by omega
      have h8 : x^3 ≤ 2011^3 := by
        have h9 : x ≤ 2011 := h7
        have h10 : x^3 ≤ 2011^3 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals linarith
        linarith
      have h11 : 2011^3 < 2012^3 := by norm_num
      linarith
    have h6 : x = 2012 := by 
      linarith
    exact h6
  exact h2