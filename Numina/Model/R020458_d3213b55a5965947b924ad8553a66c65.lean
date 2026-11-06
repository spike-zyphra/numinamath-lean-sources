import Mathlib

theorem number_theory_209296 {n : ℕ} (hn : n.divisors.card = 6) (hnp : n.primeFactors.card = 2)
    (hsum : ∑ d ∈ n.divisors, d = 248) : n = 175 := by
  have h1 : n ≠ 0 := by
    by_contra h
    rw [h] at hn hnp
    simp at hn hnp
  have h2 : n > 0 := by 
    by_contra h 
    have hn0 : n = 0 := by linarith 
    tauto 
  have h3 : n ≤ 248 := by 
    have h4 : ∑ d in n.divisors, d ≥ n := by 
      have hn1 : n ∈ n.divisors := by
        simp [Nat.mem_divisors, h1]
        all_goals linarith 
      have hn2 : ∑ d in n.divisors, d ≥ n := by 
        apply Finset.single_le_sum (fun x hx => by simp) hn1
      linarith
    linarith 
  interval_cases n <;> norm_num [Nat.divisors, Finset.mem_coe, Nat.primeFactors, Nat.primeFactorsList] at hn hnp hsum 
  <;> tauto