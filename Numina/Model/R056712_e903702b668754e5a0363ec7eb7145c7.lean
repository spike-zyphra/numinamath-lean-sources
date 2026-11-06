import Mathlib

theorem number_theory_6110 {n : ℕ} (hn : n = 2^19 - 2^10 + 1) :
    n.primeFactors.card = 3 → ∑ p ∈ n.primeFactors, p % 4 = 3 := by 
  intro h
  rw [hn] at *
  native_decide
  all_goals try { native_decide }