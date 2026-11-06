import Mathlib

def f (n m : ℕ) := n * (n + 1) / 2 + m

theorem number_theory_43773 :
    ∃ n m, f n m = 2002 ∧ n > 0 ∧ m > 0 := by
  use 62, 49
  native_decide