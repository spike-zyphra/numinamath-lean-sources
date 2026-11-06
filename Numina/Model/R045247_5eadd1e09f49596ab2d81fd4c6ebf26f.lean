import Mathlib

theorem number_theory_131099 (n : ℕ) (h : n % 100000 = 2050306) :
    IsLeast {x | ∃ n, x = ∑ i ∈ Finset.range 9, (n + i)} 31020156 := by
  have h1 : n % 100000 < 100000 := by 
    omega
  omega