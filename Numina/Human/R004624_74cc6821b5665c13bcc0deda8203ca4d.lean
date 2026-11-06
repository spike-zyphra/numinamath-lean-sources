import Mathlib

theorem number_theory_290683 (n : ℕ) (h : Odd n) (h' : ∑ i ∈ Finset.range 9, (n + 2 * i) = 2007) :
    n = 215 := by 
  simp [Finset.sum_range_succ] at h'
  omega