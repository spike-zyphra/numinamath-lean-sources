import Mathlib

/-
Qustion 51. If in a certain six-digit number the leftmost digit，7 is moved to the end of the number, the resulting number is 5 times smaller than the original. Find the original number.
-/
theorem Number_Theory_232855 
    (a b c d e f : ℕ)
    (A : a = 1)
    (B : b = 4)
    (C : c = 2)
    (D : d = 8)
    (E : e = 5)
    (F : f = 7) :
    7 * 10 ^ 5 + a * 10 ^ 4 + b * 10 ^ 3 + c * 10 ^ 2 + d * 10 + e =
    5 * (a * 10 ^ 5 + b * 10 ^ 4 + c * 10 ^ 3 + d * 10 ^ 2+ e * 10 + f) := by

    calc 7 * 10 ^ 5 + a * 10 ^ 4 + b * 10 ^ 3 + c * 10 ^ 2 + d * 10 + e =
    5 * (a * 10 ^ 5 + b * 10 ^ 4 + c * 10 ^ 3 + d * 10 ^ 2 + e * 10 + f) := by simp_all [Nat.pow_succ]
