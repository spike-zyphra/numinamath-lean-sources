import Mathlib

theorem number_theory_265540 (n : ℕ) (h₀ : n > 0) (h₁ : (n * (n + 1) * (n + 2) * (n + 3)) = 358800) : n + (n + 1) + (n + 2) + (n + 3) = 98 := by
  have h2 : n ≤ 100 := by
    by_contra h
    push_neg at h
    have h3 : n * (n + 1) * (n + 2) * (n + 3) > 358800 := by
      have h4 : n ≥ 101 := by linarith
      have h5 : n + 1 ≥ 102 := by omega
      have h6 : n + 2 ≥ 103 := by omega
      have h7 : n + 3 ≥ 104 := by omega
      have h8 : (n : ℕ) * (n + 1) * (n + 2) * (n + 3) ≥ 101 * 102 * 103 * 104 := by 
        have h9 : (n : ℕ) ≥ 101 := by omega
        have h10 : (n + 1 : ℕ) ≥ 102 := by omega
        have h11 : (n + 2 : ℕ) ≥ 103 := by omega
        have h12 : (n + 3 : ℕ) ≥ 104 := by omega
        have h13 : (n : ℕ) * (n + 1) * (n + 2) * (n + 3) ≥ 101 * 102 * 103 * 104 := by
          have h14 : (n : ℕ) ≥ 101 := by omega
          have h15 : (n + 1 : ℕ) ≥ 102 := by omega
          have h16 : (n + 2 : ℕ) ≥ 103 := by omega
          have h17 : (n + 3 : ℕ) ≥ 104 := by omega

          norm_num at *
          all_goals
          have h100 : (n : ℕ) * (n + 1) * (n + 2) * (n + 3) ≥ 101 * 102 * 103 * 104 := by 
            have h99 : (n : ℕ) ≥ 101 := by omega
            have h98 : (n + 1 : ℕ) ≥ 102 := by omega
            have h97 : (n + 2 : ℕ) ≥ 103 := by omega
            have h96 : (n + 3 : ℕ) ≥ 104 := by omega
            have h95 : (n : ℕ) * (n + 1) ≥ 101 * 102 := by nlinarith
            have h94 : (n + 2 : ℕ) * (n + 3) ≥ 103 * 104 := by nlinarith
            nlinarith [h95, h94]
          nlinarith
        nlinarith
      norm_num at h8
      omega
    linarith
  interval_cases n <;> omega