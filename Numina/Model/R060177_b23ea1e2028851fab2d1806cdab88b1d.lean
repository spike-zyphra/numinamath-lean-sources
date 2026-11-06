import Mathlib

theorem number_theory_5151 {n : ℕ} (hn : n = 7999999999) :
    n.primeFactors.card = 2 ∧ n.primeFactors ≠ ∅ := by 
  rw [hn]
  native_decide