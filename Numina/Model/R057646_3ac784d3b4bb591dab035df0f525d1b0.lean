import Mathlib

def seq (n : ℕ) := match n with
  | 0 => 2
  | n + 1 => seq n + n + 3

theorem algebra_214587 : seq 1994 = 1993005 := by
  native_decide