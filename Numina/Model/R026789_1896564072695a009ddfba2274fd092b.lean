import Mathlib

def sumOfDigits (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_100390 {a : ℕ → ℕ}
    (ha1 : a 1 = 1989 ^ 1989)
    (han : ∀ n > 1, a n = sumOfDigits (a (n - 1))) :
    a 5 = 9 := by 
  have h2 : a 2 = sumOfDigits (a 1) := han 2 (by norm_num)
  have h3 : a 3 = sumOfDigits (a 2) := han 3 (by norm_num)
  have h4 : a 4 = sumOfDigits (a 3) := han 4 (by norm_num)
  have h5 : a 5 = sumOfDigits (a 4) := han 5 (by norm_num)
  rw [h5, h4, h3, h2, ha1]
  native_decide