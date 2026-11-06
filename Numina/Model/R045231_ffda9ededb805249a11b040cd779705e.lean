import Mathlib

theorem algebra_240739 (s : ℕ → ℝ) (hs1: s 1 = 1992^(1/1992)) (h: ∀ n, 1≤ n → s (n+1) = ((1992)^(1/(1992:ℝ)))^(s n)) : (s 1992) < 1992 := by
  have h1 : ∀ k, s (k + 1) < 1992 := by
    intro k
    induction k with
    | zero =>
      rw [hs1]
      have h2 : (1992 : ℝ) ^ (1 / 1992 : ℝ) < (1992 : ℝ) := by
        have h3 : (1 / 1992 : ℝ) < (1 : ℝ) := by norm_num
        have h4 : (1992 : ℝ) ^ (1 / 1992 : ℝ) < (1992 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h5 : (1992 : ℝ) ^ (1 : ℝ) = (1992 : ℝ) := by simp
        linarith [h4, h5]
      linarith
    | succ k ih =>
      have h2 : 1 ≤ k + 1 := by linarith
      have h3 : s (k + 2) = ((1992 : ℝ) ^ (1 / 1992 : ℝ)) ^ (s (k + 1)) := by
        specialize h (k + 1) h2
        simpa using h
      rw [h3]
      have h4 : s (k + 1) < (1992 : ℝ) := ih
      have hc1 : (0 : ℝ) < (1992 : ℝ) ^ (1 / 1992 : ℝ) := by positivity
      have hc2 : ( (1992 : ℝ) ^ (1 / 1992 : ℝ) ) > (1 : ℝ) := by
        have h11 : (1 : ℝ) < (1992 : ℝ) := by norm_num
        have h12 : (0 : ℝ) < (1 / 1992 : ℝ) := by norm_num
        have h13 : (1992 : ℝ) ^ (1 / 1992 : ℝ) > (1 : ℝ) := by
          have h14 : (1992 : ℝ) ^ (1 / 1992 : ℝ) > (1 : ℝ) := by
            have h15 : (0 : ℝ) < (1 / 1992 : ℝ) := by norm_num
            have h16 : (1992 : ℝ) ^ (1 / 1992 : ℝ) > (1992 : ℝ) ^ (0 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_lt
              all_goals linarith
            have hc0 : (1992 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
              simp
            have h17 : (1992 : ℝ) ^ (1 / 1992 : ℝ) > (1 : ℝ) := by
              linarith [hc0, h16]
            linarith
          linarith
        linarith
      -- let's show ((1992: ℝ) ^ (1 / 1992 : ℝ)) ^ s (k + 1) < ((1992: ℝ) ^ (1 / 1992 : ℝ)) ^ (1992 : ℝ)
      -- this would be true given that s(k+1) < 1992
      -- a^x < a^y, for strictly increasing functions
      have h5 : ((1992 : ℝ) ^ (1 / 1992 : ℝ)) ^ (s (k + 1)) < ((1992 : ℝ) ^ (1 / 1992 : ℝ)) ^ (1992 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      have h6 : ((1992 : ℝ) ^ (1 / 1992 : ℝ)) ^ (1992 : ℝ) = (1992 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith [h5, h6]

  have h1991 : 1 ≤ 1991 := by norm_num
  have h1992 : s 1992 = ((1992 : ℝ) ^ (1 / 1992 : ℝ)) ^ (s 1991) := by
    specialize h 1991 h1991
    simpa using h
  have h1991s : s 1991 < (1992 : ℝ) := h1 1990
  rw [h1992]
  -- prove that ((1992: ℝ) ^ (1 / 1992 : ℝ)) ^ s 1991 < 1992
  have h7 : ((1992 : ℝ) ^ (1 / 1992 : ℝ) ) ^ s 1991 < ((1992 : ℝ) ^ (1 / 1992 : ℝ) ) ^ (1992 : ℝ) := by
    have hc1 : (0 : ℝ) < (1992 : ℝ) ^ (1 / 1992 : ℝ) := by positivity
    have hc2 : ( (1992 : ℝ) ^ (1 / 1992 : ℝ) ) > (1 : ℝ) := by
      have h11 : (1 : ℝ) < (1992 : ℝ) := by norm_num
      have h12 : (0 : ℝ) < (1 / 1992 : ℝ) := by norm_num
      have h13 : (1992 : ℝ) ^ (1 / 1992 : ℝ) > (1 : ℝ) := by
        have h14 : (1992 : ℝ) ^ (1 / 1992 : ℝ) > (1 : ℝ) := by
          have h15 : (0 : ℝ) < (1 / 1992 : ℝ) := by norm_num
          have h16 : (1992 : ℝ) ^ (1 / 1992 : ℝ) > (1992 : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals linarith
          have hc0 : (1992 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
            simp
          have h17 : (1992 : ℝ) ^ (1 / 1992 : ℝ) > (1 : ℝ) := by
            linarith [hc0, h16]
          linarith
        linarith
      linarith
    apply Real.rpow_lt_rpow_of_exponent_lt
    all_goals linarith
  have h8 : ((1992 : ℝ) ^ (1 / 1992 : ℝ) ) ^ (1992 : ℝ) = (1992 : ℝ) := by
    rw [← Real.rpow_mul]
    norm_num
    all_goals
      norm_num
  linarith [h7, h8]