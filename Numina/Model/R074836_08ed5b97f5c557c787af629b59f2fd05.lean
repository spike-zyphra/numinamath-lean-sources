import Mathlib

theorem number_theory_176116 {n : ℕ} (hn : n = 6 * 5 * 4 * 3 * 2 * 1) :
    n.divisors.card = 30 := by 
  rw [hn]
  native_decide