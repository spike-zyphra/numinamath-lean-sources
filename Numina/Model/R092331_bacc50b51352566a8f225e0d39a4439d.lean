import Mathlib

def isLucky (n : ℕ) := 7 ∣ (Nat.digits 10 n).sum

theorem number_theory_184315 :
    ∃ k, isLucky k ∧ isLucky (k + 1) := by
  use 69999
  constructor
  · -- Show that 69999 is lucky
    unfold isLucky
    native_decide
  · -- Show that 70000 is lucky
    unfold isLucky
    native_decide