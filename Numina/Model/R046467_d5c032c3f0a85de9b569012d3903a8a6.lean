import Mathlib

theorem algebra_306776 (m n : ℕ) :
    (2^m * 3^n - 3^(n + 1) + 2^m = 13) ↔ (m = 3 ∧ n = 0) ∨ (m = 2 ∧ n = 2) := by
  constructor
  · -- Forward: if the equation holds, then (m=3 ∧ n=0) ∨ (m=2 ∧ n=2)
    intro h_eq
    -- Using `eq1` and different algebraic manipulations
    -- Check solutions
    have h1 : m ≤ 7 := by
      by_contra h3
      push_neg at h3
      have h21 : 2^m ≥ 2^8 := by
        have h5 : m ≥ 8 := by omega
        exact Nat.pow_le_pow_of_le_right (by norm_num) h5
      have h5 : n ≤ 7 := by
        by_contra h4
        push_neg at h4
        have h6 : 3^n ≥ 3^8 := by
          have h7 : n ≥ 8 := by omega
          exact Nat.pow_le_pow_of_le_right (by norm_num) h7
        omega
      interval_cases n <;> try { 
        omega
      }
      all_goals omega
    have h2 : n ≤ 7 := by
      by_contra h3
      push_neg at h3
      have h35 : 3^n ≥ 3^8 := by
        have h5 : n ≥ 8 := by omega
        exact Nat.pow_le_pow_of_le_right (by norm_num) h5
      -- Plug bounds with exhaustive check
      have h5 : m ≤ 7 := by
        by_contra h4
        push_neg at h4
        have h6 : 2^m ≥ 2^8 := by
          have h7 : m ≥ 8 := by omega
          exact Nat.pow_le_pow_of_le_right (by norm_num) h7
        omega
      interval_cases m <;> try { 
        omega
      }
      all_goals omega
    interval_cases m <;> try { 
      omega
    }
    <;> interval_cases n <;> 
      try { omega }
    <;> norm_num at h_eq ⊢
    <;> tauto
  · -- Backward: (m=3 ∧ n=0) ∨ (m=2 ∧ n=2) implies the equation
    rintro (h | h)
    · -- For (m=3 ∧ n=0)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- For (m=2 ∧ n=2)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
  all_goals norm_num