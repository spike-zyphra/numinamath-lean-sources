import Mathlib

/- The sum of 27 consecutive positive integers is $3^7$. What is their median? -/
theorem algebra_21685 (n : ℕ) (hn : 0 < n) (h : ∑ i ∈ Finset.range 27, (n + i) = 3^7) :
    (n + 13) = 81 := by 
  simp_all [Finset.sum_range_succ, pow_succ]
  omega