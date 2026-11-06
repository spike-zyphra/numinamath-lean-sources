import Mathlib

theorem amc_number_theory_1156 (A M C : ℕ) (h₀ : (100 * A + 10 * M + C) * (A + M + C) = 2005) : A = 4 := by 
  have h3 : (100 * A + 10 * M + C) ∣ 2005 := by 
    use (A + M + C)
    linarith
  have h5 : (100 * A + 10 * M + C) = 1 ∨ (100 * A + 10 * M + C) = 5 ∨ (100 * A + 10 * M + C) = 401 ∨ (100 * A + 10 * M + C) = 2005 := by
    have h7 : (100 * A + 10 * M + C) ∣ 2005 := h3 
    have h8 : (100 * A + 10 * M + C) = 1 ∨ (100 * A + 10 * M + C) = 5 ∨ (100 * A + 10 * M + C) = 401 ∨ (100 * A + 10 * M + C) = 2005 := by
      have h9 : (100 * A + 10 * M + C) ≤ 2005 := by 
        exact Nat.le_of_dvd (by norm_num) h7 
      interval_cases h10 : (100 * A + 10 * M + C) <;> norm_num at h7 ⊢ 
    tauto 
  rcases h5 with h6 | h6 | h6 | h6 
  · -- Case where 100A + 10M + C = 1 
    rw [h6] at h₀ 
    have h8 : A + M + C = 2005 := by 
      nlinarith 
    exfalso 
    have h9 : A = 0 := by 
      omega 
    have h10 : M = 0 := by 
      omega 
    have h11 : C = 1 := by 
      omega 
    omega 
  · -- Case where 100A + 10M + C = 5 
    rw [h6] at h₀ 
    have h8 : A + M + C = 401 := by 
      nlinarith 
    have h9 : A = 0 := by 
      omega 
    omega 
  · -- Case where 100A + 10M + C = 401 
    rw [h6] at h₀ 
    have h7 : A + M + C = 5 := by 
      nlinarith 
    have h8 : A = 4 := by 
      omega 
    exact h8 
  · -- Case where 100A + 10M + C = 2005 
    rw [h6] at h₀ 
    have h7 : A + M + C = 1 := by 
      nlinarith 
    exfalso 
    have h9 : A ≥ 20 := by 
      omega 
    omega