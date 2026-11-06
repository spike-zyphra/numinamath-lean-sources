import Mathlib

theorem number_theory_231475 (A : ℕ) (hA : A = 10^81 - 1) :
    (Nat.digits 10 (A^2)).sum = 729 := by 
  rw [hA]
  native_decide