import Mathlib

def f (n : ℕ) := if n = 0 then 1 else (3 * (f (n - 1)) + 5)

theorem other_49316 : (Nat.digits 9 (f 10)).sum = 21 := by
  native_decide