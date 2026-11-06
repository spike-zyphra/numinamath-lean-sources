import Mathlib

theorem number_theory_122898 {A B C D : ℕ} (hA : A = 2012^2012)
    (hB : B = (Nat.digits 10 A).sum) (hC : C = (Nat.digits 10 B).sum)
    (hD : D = (Nat.digits 10 C).sum) : D = 7 := by 
  rw [hA] at hB
  rw [hB] at hC
  rw [hC] at hD
  rw [hD]
  native_decide