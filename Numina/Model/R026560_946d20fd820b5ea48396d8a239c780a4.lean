import Mathlib

theorem number_theory_326476 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k : ℕ, (Finset.sum (Finset.Icc 1 n) fun i => i^2) / n = k^2} 1 ∧
    ∃ m n : ℕ, m > 1 ∧ n > 1 ∧ ∃ p q : ℕ, (Finset.sum (Finset.Icc 1 m) fun i => i^2) / m = p^2 ∧
      (Finset.sum (Finset.Icc 1 n) fun i => i^2) / n = q^2 := by
  constructor
  · -- Show 1 is the least element
    constructor
    · -- Show 1 is in the set
      constructor
      · norm_num
      · use 1
        all_goals norm_num [Finset.sum_Icc_succ_top]
    · -- Show there is no smaller element
      intro n hn
      rcases hn with ⟨hn_pos, k, hk⟩
      by_contra h
      push_neg at h
      have : n < 1 := by linarith
      linarith
  · -- Show existence of the next two positive integers
    use 337, 337
    constructor
    · -- Show m > 1
      norm_num
    constructor
    · -- Show n > 1
      norm_num
    use 195, 195
    constructor
    · -- Show the first equality
      native_decide
    · -- Show the second equality 
      native_decide