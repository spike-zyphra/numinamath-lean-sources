import Mathlib

theorem number_theory_3481 {n : ℕ} (hn : n = 2018415) :
    ∑ p in n.primeFactors, p = 3 + 5 + 7 + 47 + 409 := by 
  rw [hn]
  native_decide