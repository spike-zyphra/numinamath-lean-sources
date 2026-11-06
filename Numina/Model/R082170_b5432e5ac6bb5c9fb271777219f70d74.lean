import Mathlib

theorem algebra_16698 {n : ℕ} (hn : n = 24) :
    n.divisors.card = 8 := by 
  rw [hn]
  native_decide