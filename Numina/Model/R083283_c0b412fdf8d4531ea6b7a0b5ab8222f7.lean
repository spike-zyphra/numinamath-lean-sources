import Mathlib

theorem number_theory_204789 {n : ℕ} (hn : n = 999973) :
    ∑ p in n.primeFactors, p = 171 := by
  rw [hn]
  native_decide