import Mathlib

def sumOfDigits (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_222119 {a : ℕ → ℕ}
    (ha1 : a 1 = 1989 ^ 1989)
    (han : ∀ n, a (n + 1) = sumOfDigits (a n)) :
    a 5 = 9 := by
  have ha2 : a 2 = sumOfDigits (a 1) := han 1
  have ha3 : a 3 = sumOfDigits (a 2) := han 2
  have ha4 : a 4 = sumOfDigits (a 3) := han 3
  have ha5 : a 5 = sumOfDigits (a 4) := han 4
  rw [ha5, ha4, ha3, ha2, ha1]
  native_decide