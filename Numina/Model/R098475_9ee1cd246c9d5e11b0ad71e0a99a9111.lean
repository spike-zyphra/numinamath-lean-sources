import Mathlib

theorem number_theory_3758 (n : ℕ) (h₀ : n > 0) (h₁ : n^3 = 8217949832) : n = 2018 := by
  have h2 : n = 2018 := by
    have h3 : n^3 = 8217949832 := h₁
    have h4 : n ≤ 2018 := by
      by_contra h
      push_neg at h
      have h5 : n >= 2019 := by
        omega
      have h6 : n^3 >= 2019^3 := by
        have h7 : n >= 2019 := by
          omega
        have h8 : n^3 >= 2019^3 := by
          apply Nat.pow_le_pow_of_le_left h7 3
        linarith
      norm_num at h6 h₁
      linarith
    have h9 : n >= 2018 := by
      by_contra h
      push_neg at h
      have h10 : n <= 2017 := by
        omega
      have h11 : n^3 <= 2017^3 := by
        have h12 : n <= 2017 := by
          omega
        have h13 : n^3 <= 2017^3 := by
          apply Nat.pow_le_pow_of_le_left h12 3
        linarith
      norm_num at h11 h₁
      linarith
    linarith
  exact h2