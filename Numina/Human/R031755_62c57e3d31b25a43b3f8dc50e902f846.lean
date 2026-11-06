import Mathlib

theorem number_theory_227175 :
    IsLeast {n | ∃ k, n = ∑ i ∈ Finset.range 5, (2 * i + 2 * k) ∧ 7 ∣ n} 70 := by
  constructor
  · -- First, let's show that 70 belongs to the set
    use 5
    constructor
    · -- Compute the sum when k = 5
      norm_num [Finset.sum_range_succ]
    · -- Verify that 70 is divisible by 7
      norm_num
  · -- Now we need to show that no smaller positive integer belongs to the set
    intro n hn
    rcases hn with ⟨k, h_eq, h_div⟩
    have h_sum : n = 10 * k + 20 := by
      simp [Finset.sum_range_succ] at h_eq
      linarith
    rw [h_sum] at h_div
    omega -- Automated tactic to solve integer arithmetic goals