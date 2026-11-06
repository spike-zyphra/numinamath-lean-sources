import Mathlib

theorem number_theory_114513 (n : ℕ) (hn : n > 1) :
    ∃ k, Odd k ∧ ∀ i ∈ Finset.range n, Odd (k + 2 * i) ∧
    n^2 = ∑ i ∈ Finset.range n, (k + 2 * i) := by

  use 1
  constructor
  · -- Show that 1 is odd
    exact ⟨0, by norm_num⟩
  · -- Show that for all i in range n, 1 + 2i is odd and the sum equals n^2
    intro i hi
    constructor
    · -- Show that 1 + 2 * i is odd 
      use i
      all_goals
        ring_nf
    · -- Show that n^2 = ∑ i in Finset.range n, (1 + 2 * i)
      have h2 : ∑ i in Finset.range n, (1 + 2 * i) = n ^ 2 := by 
        have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (1 + 2 * i) = n ^ 2 := by
          intro n
          induction n with 
          | zero => 
            simp 
          | succ n ih => 
            rw [Finset.sum_range_succ, ih]
            all_goals ring_nf 
        specialize h2 n
        simpa using h2 
      linarith [h2]