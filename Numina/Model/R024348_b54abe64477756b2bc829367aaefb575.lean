import Mathlib

theorem algebra_304763 : (Nat.digits 10 (Nat.floor ((9.4 : ℝ)^10 * 5^25))).length = 28 := by
  have h1 : Nat.floor ((9.4 : ℝ)^10 * 5^25) = (94^10 * 5^25) / 10^10 := by 
    norm_num [Nat.floor_eq_iff]
  have h3 : (94^10 * 5^25 : ℕ) / 10^10 = 47^10 * 5^15 := by 
    norm_num
  rw [h1]
  rw [h3]
  have h27 : (47 ^ 10 * 5 ^ 15 : ℕ) ≥ (10 ^ 27 : ℕ) := by 
    norm_num
  have h28 : (47 ^ 10 * 5 ^ 15 : ℕ) < (10 ^ 28 : ℕ) := by 
    norm_num
  have h7 : (Nat.digits 10 (47 ^ 10 * 5 ^ 15 )).length = 28 := by
    have h14 : (Nat.digits 10 (47 ^ 10 * 5 ^ 15 )).length = 
      Nat.log 10 (47 ^ 10 * 5 ^ 15) + 1 := by 
        rw [Nat.digits_len]
        all_goals
          try omega
    rw [h14]
    have h15 : Nat.log 10 (47 ^ 10 * 5 ^ 15) = 27 := by
      have h16 : (47 ^ 10 * 5 ^ 15 : ℕ) ≥ (10 ^ 27 : ℕ) := h27
      have h17 : (47 ^ 10 * 5 ^ 15 : ℕ) < (10 ^ 28 : ℕ) := h28
      have h18 : Nat.log 10 (47 ^ 10 * 5 ^ 15) = 27 := by
        rw [Nat.log_eq_iff]
        all_goals
          try omega
      exact h18
    omega
  exact h7