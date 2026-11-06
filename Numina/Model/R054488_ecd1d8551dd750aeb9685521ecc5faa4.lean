import Mathlib

def sumOfDigits (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_53315 {a : ℕ → ℕ}
    (ha1 : a 1 = 1989 ^ 1989)
    (han : ∀ n > 1, a n = sumOfDigits (a (n - 1))) :
    a 5 = 9 := by
  have ha2 : a 2 = sumOfDigits (a 1) := han 2 (by decide)
  rw [ha1] at ha2
  have ha3 : a 3 = sumOfDigits (a 2) := han 3 (by decide)
  rw [ha2] at ha3
  have ha4 : a 4 = sumOfDigits (a 3) := han 4 (by decide)
  rw [ha3] at ha4
  have ha5 : a 5 = sumOfDigits (a 4) := han 5 (by decide)
  rw [ha4] at ha5
  rw [ha5]
  <;> native_decide
  <;> native_decide