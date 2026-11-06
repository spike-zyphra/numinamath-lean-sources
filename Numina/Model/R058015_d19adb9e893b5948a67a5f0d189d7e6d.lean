import Mathlib

theorem algebra_269811 : ∃ n : ℕ, Even n ∧ ∀ i ∈ Finset.range 10, Even (n + 2 * i) ∧ ∑ i ∈ Finset.range 10, (n + 2 * i) = 190 := by
  use 10
  constructor
  · -- Show that 10 is even
    exact Nat.even_iff.mpr (by norm_num)
  · -- Show that for each i in Finset.range 10, both conditions hold
    intro i hi
    have h1 : i < 10 := by
      simp [Finset.mem_range] at hi 
      linarith 
    constructor
    · -- Show that 10 + 2*i is even for each i
      have h2 : Even (10 + 2 * i) := by 
        use (5 + i)
        ring 
      exact h2 
    · -- Show that sum from i ∈ range 10, (10 + 2i) equals 190
      norm_num [Finset.sum_range_succ]