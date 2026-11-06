import Mathlib


theorem number_theory_218346 (x y : ℕ) :
    x^2 - y^2 = 31 ∨ x^2 - y^2 = 303 ↔
    (x = 16 ∧ y = 15) ∨ (x = 152 ∧ y = 151) ∨ (x = 52 ∧ y = 49) := by
  constructor
  · -- Assume x^2 - y^2 = 31 or 303, prove the disjunction of the solutions
    rintro (h | h)
    · -- When x^2 - y^2 = 31
      have h1 : x ^ 2 = y ^ 2 + 31 := by
        omega
      have h2 : x > y := by
        by_contra h3
        push_neg at h3
        have h4 : x ≤ y := by linarith
        have h5 : x ^ 2 ≤ y ^ 2 := by nlinarith
        omega
      have h3 : (x : ℕ) > (y : ℕ) := h2
      have h4 : (x : ℤ) ^ 2 - (y : ℤ) ^ 2 = 31 := by
        have h5 : (x : ℤ) ^ 2 = (y : ℤ) ^ 2 + 31 := by
          exact_mod_cast (show x ^ 2 = y ^ 2 + 31 by linarith)
        linarith
      have h5 : ((x : ℤ) - (y : ℤ)) * ((x : ℤ) + (y : ℤ)) = 31 := by
        nlinarith
      have h6 : (x : ℤ) - (y : ℤ) = 1 ∨ (x : ℤ) - (y : ℤ) = 31 := by
        have h7 : ((x : ℤ) - (y : ℤ)) * ((x : ℤ) + (y : ℤ)) = 31 := h5
        have h8 : (x : ℤ) - (y : ℤ) ∣ 31 := by
          use (x + (y : ℤ))
          all_goals linarith
        have h9 : (x : ℤ) - (y : ℤ) ∣ 31 := h8
        have h10 : (x : ℤ) - (y : ℤ) ≤ 31 := by
          apply Int.le_of_dvd (by norm_num) h9
        have h11 : (x : ℤ) - (y : ℤ) ≥ -31 := by
          have h12 : -( (x : ℤ) - (y : ℤ) ) ∣ 31 := by
            exact Int.neg_dvd.2 h9
          have h13 : -( (x : ℤ) - (y : ℤ) ) ≤ 31 := by
            apply Int.le_of_dvd (by norm_num) h12
          omega
        interval_cases h14 : (x : ℤ) - (y : ℤ) <;> omega
      rcases h6 with h6 | h6
      · -- When x - y = 1
        have h7 : (x : ℤ) + (y : ℤ) = 31 := by
          rw [h6] at h5
          linarith
        have h8 : x = 16 := by
          omega
        have h9 : y = 15 := by
          omega
        left
        simp [h8, h9]
      · -- When x - y = 31
        have h7 : (x : ℤ) + (y : ℤ) = 1 := by
          rw [h6] at h5
          linarith
        omega
    · -- When x^2 - y^2 = 303
      have h1 : x ^ 2 = y ^ 2 + 303 := by
        omega
      have h2 : x > y := by
        by_contra h3
        push_neg at h3
        have h4 : x ≤ y := by linarith
        have h5 : x ^ 2 ≤ y ^ 2 := by nlinarith
        omega
      have h3 : (x : ℕ) > (y : ℕ) := h2
      have h4 : (x : ℤ) ^ 2 - (y : ℤ) ^ 2 = 303 := by
        have h5 : (x : ℤ) ^ 2 = (y : ℤ) ^ 2 + 303 := by
          exact_mod_cast (show x ^ 2 = y ^ 2 + 303 by linarith)
        linarith
      have h5 : ((x : ℤ) - (y : ℤ)) * ((x : ℤ) + (y : ℤ)) = 303 := by
        nlinarith
      have h6 : (x : ℤ) - (y : ℤ) = 1 ∨ (x : ℤ) - (y : ℤ) = 3 := by
        have h7 : ((x : ℤ) - (y : ℤ)) * ((x : ℤ) + (y : ℤ)) = 303 := h5
        have h8 : (x : ℤ) - (y : ℤ) ∣ 303 := by
          use (x + (y : ℤ))
          all_goals linarith
        have h9 : (x : ℤ) - (y : ℤ) ∣ 303 := h8
        have h10 : (x : ℤ) - (y : ℤ) ≤ 303 := by
          apply Int.le_of_dvd (by norm_num) h9
        have h11 : (x : ℤ) - (y : ℤ) ≥ -303 := by
          have h12 : -( (x : ℤ) - (y : ℤ) ) ∣ 303 := by
            exact Int.neg_dvd.2 h9
          have h13 : -( (x : ℤ) - (y : ℤ) ) ≤ 303 := by
            apply Int.le_of_dvd (by norm_num) h12
          omega
        interval_cases h14 : (x : ℤ) - (y : ℤ) <;> omega
      rcases h6 with h6 | h6
      · -- When x - y = 1
        have h7 : (x : ℤ) + (y : ℤ) = 303 := by
          rw [h6] at h5
          linarith
        have h8 : x = 152 := by
          omega
        have h9 : y = 151 := by
          omega
        right
        left
        simp [h8, h9]
      · -- When x - y = 3
        have h7 : (x : ℤ) + (y : ℤ) = 101 := by
          rw [h6] at h5
          linarith
        have h8 : x = 52 := by
          omega
        have h9 : y = 49 := by
          omega
        right
        right
        simp [h8, h9]
  · -- Assume the disjunction of the solutions, prove x^2 - y^2 = 31 or 303
    rintro (h | h | h)
    · -- When (x = 16 ∧ y = 15)
      rcases h with ⟨hx, hy⟩
      have h1 : x^2 - y^2 = 31 := by
        simp [hx, hy]
      left
      exact h1
    · -- When (x = 152 ∧ y = 151)
      rcases h with ⟨hx, hy⟩
      have h1 : x^2 - y^2 = 303 := by
        simp [hx, hy]
      right
      exact h1
    · -- When (x = 52 ∧ y = 49)
      rcases h with ⟨hx, hy⟩
      have h1 : x^2 - y^2 = 303 := by
        simp [hx, hy]
      right
      exact h1