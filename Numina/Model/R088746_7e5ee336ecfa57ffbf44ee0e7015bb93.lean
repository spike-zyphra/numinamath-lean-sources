import Mathlib

theorem number_theory_192935 (n : ℕ) (h₀ : n = 6666666666666667) :
    (Nat.digits 10 (n ^ 2)).sum = 193 := by 
  rw [h₀]
  native_decide