import Mathlib

theorem algebra_132324 (x : ℕ) : 3 * 16 ^ x + 2 * 81 ^ x = 5 * 36 ^ x ↔ x = 0 := by
  constructor
  · -- Assume the equation holds, prove x = 0
    intro h_eq
    by_cases h2 : x > 0
    · -- Assume x > 0 
      have eq4 : (3 * 16 ^ x + 2 * 81 ^ x) % 4 = (5 * 36 ^ x) % 4 := by 
        omega
      have eq5 : (3 * 16 ^ x + 2 * 81 ^ x) % 4 = 2 := by
        have h3 : x > 0 := h2 
        have h4 : (16 : ℕ) ^ x % 4 = 0 := by 
          have h6 : ∀ m : ℕ, (16 : ℕ) ^ (m + 1) % 4 = 0 := by 
            intro m
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              simp [Nat.pow_succ] at ih ⊢
              omega 
          specialize h6 (x - 1)
          have h7 : x - 1 + 1 = x := by omega 
          rw [h7] at h6 
          omega 
        have h5 : (81 : ℕ) ^ x % 4 = 1 := by
          have h6 : ∀ m : ℕ, (81 : ℕ) ^ m % 4 = 1 := by
            intro m 
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              simp [Nat.pow_succ] at ih ⊢
              omega 
          specialize h6 x 
          simpa using h6
        omega
      have eq6 : (5 * 36 ^ x) % 4 = 0 := by 
        have h3 : x > 0 := h2
        have h4 : (36 : ℕ) ^ x % 4 = 0 := by 
          have h6 : ∀ m : ℕ, (36 : ℕ) ^ (m + 1) % 4 = 0 := by 
            intro m 
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              simp [Nat.pow_succ] at ih ⊢
              omega 
          specialize h6 (x - 1)
          have h7 : x - 1 + 1 = x := by omega 
          rw [h7] at h6 
          omega 
        omega 
      omega
    · -- Assume x ≤ 0 
      have h3 : x = 0 := by
        omega 
      assumption
  · -- Assume x = 0, prove the equation 
    intro h_eq 
    rw [h_eq]
    all_goals norm_num