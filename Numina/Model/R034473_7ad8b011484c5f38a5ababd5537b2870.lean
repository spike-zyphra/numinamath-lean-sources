import Mathlib

theorem number_theory_79901 (x : ℤ) :
    IsSquare (x * (x + 1) * (x + 7) * (x + 8)) ↔
    x = -9 ∨ x = -8 ∨ x = -7 ∨ x = -4 ∨ x = -1 ∨ x = 0 ∨ x = 1 := by
  constructor
  · -- Assume x * (x + 1) * (x + 7) * (x + 8) is a perfect square, prove x is in the set.
    intro h
    have h2 : IsSquare (x * (x + 1) * (x + 7) * (x + 8)) := h
    rcases h2 with ⟨k, hk⟩
    have h3 : (2 * (x ^ 2 + 8 * x) + 7 : ℤ) ^ 2 - 4 * k ^ 2 = 49 := by
      nlinarith [sq_nonneg (x ^ 2 + 8 * x), sq_nonneg (k ^ 2)]
    have h4 : ((2 * (x ^ 2 + 8 * x) + 7 : ℤ) - 2 * k) * ((2 * (x ^ 2 + 8 * x) + 7 : ℤ) + 2 * k) = 49 := by
      nlinarith
    have h5 : ((2 * (x ^ 2 + 8 * x) + 7 : ℤ) - 2 * k) ∣ 49 := by
      use ((2 * (x ^ 2 + 8 * x) + 7 : ℤ) + 2 * k)
      all_goals
        nlinarith
    have h6 : ((2 * (x ^ 2 + 8 * x) + 7 : ℤ) - 2 * k) ∣ 49 := h5
    have h7 : ((2 * (x ^ 2 + 8 * x) + 7 : ℤ) - 2 * k) ≤ 49 := by
      exact Int.le_of_dvd (by norm_num) h6
    have h8 : ((2 * (x ^ 2 + 8 * x) + 7 : ℤ) - 2 * k) ≥ -49 := by
      have h8 : -((2 * (x ^ 2 + 8 * x) + 7 : ℤ) - 2 * k) ∣ 49 := by
        exact Int.neg_dvd.2 h6
      have h9 : -((2 * (x ^ 2 + 8 * x) + 7 : ℤ) - 2 * k) ≤ 49 := by
        exact Int.le_of_dvd (by norm_num) h8
      linarith
    interval_cases h9 : ((2 * (x ^ 2 + 8 * x) + 7 : ℤ) - 2 * k) <;> try { 
      omega
    } <;> try { 
      have h10 : x ≤ 10 := by nlinarith
      have h11 : x ≥ -10 := by nlinarith
      interval_cases x <;> try { 
        omega
      } <;> try { 
        norm_num at hk
        all_goals
          have : k ≤ 20 := by nlinarith
          have : k ≥ -20 := by nlinarith
          interval_cases k <;> omega
      }
    }
  · -- Assume x is in the set, prove x * (x + 1) * (x + 7) * (x + 8) is a perfect square
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- x = -9
      native_decide
    · -- x = -8
      native_decide
    · -- x = -7
      native_decide
    · -- x = -4
      native_decide
    · -- x = -1
      native_decide
    · -- x = 0
      native_decide
    · -- x = 1
      native_decide