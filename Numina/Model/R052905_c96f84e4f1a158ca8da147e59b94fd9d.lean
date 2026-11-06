import Mathlib

theorem number_theory_120241 {A : ℕ} (hA : A = 13223140496) :
    IsSquare (10 ^ (Nat.digits 10 A).length * A + A) := by 
  rw [hA]
  native_decide