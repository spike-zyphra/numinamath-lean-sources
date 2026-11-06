import Mathlib

/-Let $S(k)$ denote the sum of the digits of a natural number $k$ in base 10.
If a natural number $x$ satisfies the equation $x + S(x) + S(S(x)) + S(S(S(x))) = 50$, show that $x=26$.-/

theorem number_theory_636434 (x: ℕ) (h: x + (Nat.digits 10 x).sum +
(Nat.digits 10 ((Nat.digits 10 x).sum)).sum + (Nat.digits 10 ((Nat.digits 10 x).sum)).sum = 50): x = 26 := by

  have lx: x ≤ 50 := by omega
  by_contra! ne
  interval_cases x
  all_goals simp at h
  tauto