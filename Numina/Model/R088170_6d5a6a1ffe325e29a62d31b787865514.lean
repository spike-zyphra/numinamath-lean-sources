import Mathlib

theorem number_theory_130097 {n : ℕ} (hn : n = 5 * 4 * 3 * 2) :
    n.divisors.card = 16 := by 
  rw [hn]
  native_decide