import Mathlib

theorem number_theory_164368 : ∃ n, Odd n ∧ ∀ i ∈ Finset.range 31, Odd (n + 2 * i) ∧ ∑ i ∈ Finset.range 31, (n + 2 * i) = 2015 := by
  use 35
  constructor
  · -- Show that 35 is odd
    exact Nat.odd_iff.mpr (by norm_num)
  · -- Show that all terms in the summation are odd and the sum equals 2015
    intro i hi
    constructor
    · -- Show that 35 + 2 * i is odd
      have h1 : i ∈ Finset.range 31 := hi
      rw [Finset.mem_range] at h1
      have h2 : i < 31 := h1
      exact ⟨17 + i, by ring⟩
    · -- Show the sum is 2015
      native_decide