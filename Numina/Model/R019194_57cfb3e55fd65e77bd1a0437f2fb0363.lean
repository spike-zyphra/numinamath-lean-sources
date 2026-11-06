import Mathlib

open Real
open scoped BigOperators

theorem inequalities_206266 (n : ℕ) : 2^n > n := by 
  have h1 : ∀ n : ℕ, 2^n > n := by
    intro n
    induction n with
    | zero =>
      simp
    | succ k ih =>
      have h2 : (2 : ℕ) ^ (k + 1) > (k + 1 : ℕ) := by
        have h3 : (2 : ℕ) ^ (k + 1) = 2 * ((2 : ℕ) ^ k) := by ring
        rw [h3]
        by_cases h : k = 0
        · -- Case k = 0
          subst h
          all_goals norm_num
        · -- Case k > 0
          have hk1 : k ≥ 1 := by omega
          have h4 : 2 * ((2 : ℕ) ^ k) > 2 * (k : ℕ) := by
            nlinarith [ih]
          have h5 : 2 * (k : ℕ) ≥ (k + 1 : ℕ) := by
            omega
          have h6 : 2 * ((2 : ℕ) ^ k) > (k + 1 : ℕ) := by
            linarith [h4, h5]
          linarith [h6]
      exact h2
  specialize h1 n
  simpa using h1