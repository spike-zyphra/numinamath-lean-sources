import Mathlib

def a' (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | k + 1 =>
    have : k + 1 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one k)
    (a' k) * 10 ^ (Nat.digits 10 (k + 1)).length + k + 1

theorem number_theory_15433 : a' 44 % 45 = 9 := by
  native_decide