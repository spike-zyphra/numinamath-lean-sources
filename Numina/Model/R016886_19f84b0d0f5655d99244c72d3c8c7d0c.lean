import Mathlib

def crossSum (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_172788 (n : ℕ) :
    crossSum n % 9 = n % 9 := by
  dsimp [crossSum]
  show (Nat.digits 10 n).sum % 9 = n % 9
  rw [Nat.modEq_nine_digits_sum (n)]
  <;> all_goals omega