import Mathlib

theorem number_theory_73336 (n : ℕ) (hn : n = 11) :
    ¬(n ∣ Nat.choose 1000 500) := by 
  rw [hn]
  native_decide