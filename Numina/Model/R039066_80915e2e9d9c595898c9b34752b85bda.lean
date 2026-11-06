import Mathlib

theorem algebra_151111 (n : ℕ) (hn : n > 3) :
    (∑ i ∈ Finset.range (n - 2), (i + 1) * (i + 2) ^ 2 * (i + 3) : ℕ) =
    ((n - 2) * (n - 1) * n * (n + 1) * (2 * n - 1) / 10 : ℚ) := by
  have h3 : n ≥ 4 := by omega
  have eq : (∑ i ∈ Finset.range (n - 2), (i + 1) * (i + 2) ^ 2 * (i + 3) : ℕ) =
      ((n - 2) * (n - 1) * n * (n + 1) * (2 * n - 1) / 10 : ℚ) := by 
    have eq1 : ∀ (k : ℕ), (∑ i ∈ Finset.range (k - 2), (i + 1) * (i + 2) ^ 2 * (i + 3) : ℕ) =
          ((k - 2 : ℤ) * (k - 1 : ℤ) * (k : ℤ) * (k + 1 : ℤ) * (2 * k - 1 : ℤ) / 10 : ℚ) := by 
      intro k 
      by_cases hk : k < 4 
      · interval_cases k <;> norm_num 
      · -- Case k ≥ 4
        have hk1 : k ≥ 4 := by omega 
        have eq4 : k ≥ 4 := by omega 
        have eq5 : ∀ (k : ℕ), k ≥ 4 → (∑ i ∈ Finset.range (k - 2), (i + 1) * (i + 2) ^ 2 * (i + 3) : ℕ) =
          ((k - 2 : ℤ) * (k - 1 : ℤ) * (k : ℤ) * (k + 1 : ℤ) * (2 * k - 1 : ℤ) / 10 : ℚ) := by 
          intro k hk 
          induction k with 
          | zero => 
            omega 
          | succ k ih =>
            cases k with 
            | zero => 
              norm_num at *
            | succ k => 
              cases k with 
              | zero => 
                norm_num at *
              | succ k => 
                cases k with 
                | zero => 
                  norm_num at *
                | succ k => 
                  cases k with 
                  | zero => 
                    norm_num at *
                  | succ k => 
                    simp [Finset.sum_range_succ] at ih ⊢ 
                    all_goals 
                      norm_num at ih ⊢ 
                      <;> ring_nf at ih ⊢ 
                      -- <;> norm_num at ih ⊢
                      <;> linarith 
        specialize eq5 k eq4 
        simpa using eq5 
    specialize eq1 n
    simpa using eq1
  simpa using eq