import Mathlib

open Finset

/- If $\overline{2a}\times \overline{3bc}=6657$, where $a$, $b$, $c$ represent non-zero digits, then $\overline{abc}=$ ___          ___ . -/
theorem number_theory_632030 (a b c : ℕ) (ha : a ∈ Icc 1 9) (hb : b ∈ Icc 1 9) (hc : c ∈ Icc 1 9) (h : Nat.ofDigits 10 [a, 2] * Nat.ofDigits 10 [c, b, 3] = 6657) : Nat.ofDigits 10 [c, b, a] = 117 := by
  -- There are in total 9 * 9 * 9 = 729 cases.
  -- We can use `native_decide` to check each case.
  revert c
  revert b
  revert a
  native_decide
