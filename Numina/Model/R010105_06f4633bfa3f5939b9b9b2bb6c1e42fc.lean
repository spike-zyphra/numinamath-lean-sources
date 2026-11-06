import Mathlib

theorem algebra_21516 {n : ℕ} (hn : n = 85085) :
    ∑ p in n.primeFactors, p = 53 := by
  rw [hn]
  native_decide