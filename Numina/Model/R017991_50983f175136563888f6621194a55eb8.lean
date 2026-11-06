import Mathlib

theorem algebra_5224 (n : ℤ) :
    IsSquare (n^2 + 19 * n + 192) ↔ n = 92 ∨ n = -111 ∨ n = -3 ∨ n = -16 := by
  constructor
  · -- Assume that n^2 +19 n + 192 is a square, then it can solve.
    rintro h
    rcases h with ⟨k, hk⟩
    have h1 : (2 * k - (2 * n + 19)) * (2 * k + (2 * n + 19)) = 407 := by
      nlinarith
    have h2 : (2 * k - (2 * n + 19)) ∣ 407 := by
      use (2 * k + (2 * n + 19))
      all_goals
      linarith
    have h3 : (2 * k - (2 * n + 19)) ≤ 407 := by
      apply Int.le_of_dvd (by norm_num) h2
    have h4 : (2 * k - (2 * n + 19)) ≥ -407 := by
      have h38 : (- (2 * k - (2 * n + 19))) ∣ 407 := by 
        exact Int.neg_dvd.2 h2
      have h45 : - (2 * k - (2 * n + 19)) ≤ 407 := by 
        apply Int.le_of_dvd (by norm_num) h38
      linarith
    interval_cases h5 : (2 * k - (2 * n + 19)) <;> omega
  · -- Assume n = 92 ∨ n = -111 ∨ n = -3 ∨ n = -16, then it is a square.
    rintro (h | h | h | h)
    · -- n = 92
      rw [h]
      use 102
      all_goals norm_num
    · -- n = -111
      rw [h]
      use 102
      all_goals norm_num
    · -- n = -3
      rw [h]
      use 12
      all_goals norm_num
    · -- n = -16
      rw [h]
      use 12
      all_goals norm_num