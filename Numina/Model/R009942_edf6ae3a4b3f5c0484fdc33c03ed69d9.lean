import Mathlib

theorem number_theory_5643 {n : ℕ} (hn : n = 2025023) :
    ∑ p in n.primeFactors, p = 48 := by 
  rw [hn]
  native_decide