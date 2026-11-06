import Mathlib

theorem number_theory_125122 {A : ℕ} (hA : A = 10^50 - 10^40 + 10^30 - 10^20 + 10^10 - 1) :
    (Nat.digits 10 A).sum = 270 := by
  rw [hA]
  native_decide