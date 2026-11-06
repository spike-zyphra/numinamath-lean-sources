import Mathlib

theorem number_theory_57007 {n : ℕ} (hn : n ≠ 0) :
    ∃ k, ∑ d in n.divisors, d = 2 ^ k → ∃ m, n.divisors.card = 2 ^ m := by
  use 0
  intro h
  have h1 : ∑ d in n.divisors, d = 1 := by
    simpa using h
  have h2 : n = 1 := by
    have h3 : n ≥ 1 := by 
      omega
    -- Show n ∈ n.divisors
    have h7 : n ∈ n.divisors := by
      apply Nat.mem_divisors.2
      constructor
      · exact dvd_refl n
      all_goals
        omega
    -- Show that n ≤ 1
    have h8 : n ≤ 1 := by 
      have h222 : ∑ d in n.divisors, d ≥ n := by 
        have h20 : n ∈ n.divisors := h7
        have h21 : ∑ d in n.divisors, d ≥ n := by 
          apply Finset.single_le_sum (fun i _ => by positivity) h20
        linarith
      linarith [h1, h222]
    interval_cases n <;> try tauto
  have h3 : n.divisors.card = 1 := by 
    rw [h2]
    native_decide
  use 0
  all_goals 
    rw [h3]
    all_goals 
      norm_num