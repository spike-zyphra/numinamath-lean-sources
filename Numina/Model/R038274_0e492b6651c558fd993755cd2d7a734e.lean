import Mathlib

theorem algebra_12380 : IsLeast {n : ℤ | n + 4 < 2 * (∑ i ∈ Finset.range 5, (n + i)) / (5 : ℚ)} 1 := by 
  constructor
  · -- Show 1 is in the set
    norm_num [Finset.sum_range_succ]
  · -- Show there is no smaller element in the set
    intro n hn
    have h : n + 4 < 2 * (∑ i ∈ Finset.range 5, (n + i)) / (5 : ℚ) := hn
    norm_num [Finset.sum_range_succ] at h
    have h1 : (n : ℚ) > 0 := by
      linarith
    have h2 : n > 0 := by
      exact_mod_cast h1
    linarith