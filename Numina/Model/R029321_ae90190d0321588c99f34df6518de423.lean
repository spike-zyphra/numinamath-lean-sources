import Mathlib

theorem number_theory_213772 {n : ℕ} (hn : n ≠ 0) (hnp : n.divisors.card = 6)
    (hns : ∑ d in n.divisors, d = 28) (hnp1 : n.primeFactors.card = 2) :
    n = 12 := by
  have h1 : n ≤ 28 := by
    have h3 : n ∈ n.divisors := by
      simp [Nat.mem_divisors, hn]
      all_goals tauto
    have : n ≤ ∑ d in n.divisors, d := by
      apply Finset.single_le_sum (fun x _ => by positivity) h3
    rw [hns] at this
    linarith
  interval_cases n <;> norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.mem_divisors, Nat.mem_primeFactors] at hnp hns hnp1 ⊢ <;> try { contradiction } <;> omega