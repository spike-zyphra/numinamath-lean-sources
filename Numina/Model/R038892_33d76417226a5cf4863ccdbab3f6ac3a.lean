import Mathlib

open Nat Real

theorem number_theory_265742 (n : ℕ) (hn : 0 < n) :
    logb 10 n ≥ (Nat.primeFactors n).card * logb 10 2 := by
  have h1 : 1 ≤ n := by linarith
  have h2 : n ≥ 2 ^ (Nat.primeFactors n).card := by
    have h3 : n ≥ ∏ p in Nat.primeFactors n, p := by
      have h4 : ∏ p in Nat.primeFactors n, p ∣ n := by
        apply Nat.prod_primeFactors_dvd
      have h5 : ∏ p in Nat.primeFactors n, p ≤ n := by
        exact Nat.le_of_dvd (by linarith) h4
      linarith
    have h4 : ∏ p in Nat.primeFactors n, p ≥ 2 ^ (Nat.primeFactors n).card := by
      have h5 : (∏ p in Nat.primeFactors n, p) ≥ (∏ p in Nat.primeFactors n, (2 : ℕ)) := by
        apply Finset.prod_le_prod
        ·
          intro p hp
          have h3 : p ≥ 2 := by
            have h4 : p ∈ Nat.primeFactors n := by
              simpa using hp
            have h5 : Nat.Prime p := (Nat.mem_primeFactors.mp h4).1
            exact Nat.Prime.two_le h5
          linarith
        ·
          intro p hp
          have h3 : p ≥ 2 := by
            have h4 : p ∈ Nat.primeFactors n := by
              simpa using hp
            have h5 : Nat.Prime p := (Nat.mem_primeFactors.mp h4).1
            exact Nat.Prime.two_le h5
          linarith
      have h6 : (∏ p in Nat.primeFactors n, (2 : ℕ)) = 2 ^ (Nat.primeFactors n).card := by
        rw [Finset.prod_const]
        all_goals
          simp
      linarith
    linarith
  have h3 : logb 10 (n : ℝ) ≥ logb 10 (2 ^ (Nat.primeFactors n).card : ℝ) := by
    have h4 : (2 ^ (Nat.primeFactors n).card : ℝ) > 0 := by
      positivity
    have h5 : (n : ℝ) ≥ (2 ^ (Nat.primeFactors n).card : ℝ) := by
      exact_mod_cast (show n ≥ 2 ^ (Nat.primeFactors n).card by linarith)
    have h12 : logb 10 (n : ℝ) ≥ logb 10 (2 ^ (Nat.primeFactors n).card : ℝ) := by
      apply Real.logb_le_logb_of_le
      all_goals
        try { norm_num }
        try { 
          have h4 : (2 ^ (Nat.primeFactors n).card : ℝ) > 0 := by
            positivity
          all_goals nlinarith
        }
    linarith
  have h4 : logb 10 (2 ^ (Nat.primeFactors n).card : ℝ) = (Nat.primeFactors n).card * logb 10 2 := by
    simp [logb_pow]
  linarith