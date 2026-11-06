import Mathlib
/- Let $x$ and $y$ be two natural numbers such that $x+y$ is an odd number. Prove that for any natural numbers $m$ and $n$, at least one of the numbers $(5m+n+x)$ or $(3m-n+y)$ is divisible by two. For the purpose of this problem, if $A$ and $B$ are natural numbers, $A-B$ is defined as natural number subtraction (i.e., $A-B=0$ if $A < B$). -/
theorem number_theory_640904 (x y m n : ℤ) (h1 : Odd (x + y)) : 2 ∣ 5 * m + n + x ∨ 2 ∣ 3 * m - n + y:= by
  -- Proof by contradiction
  by_contra H
  -- Simplify the contradiction hypothesis
  simp at H
  -- Extract the two conditions from the hypothesis
  rcases H with ⟨H1, H2⟩
  -- Convert the first condition to show (5m + n + x) is odd
  replace H1 : Odd (5 * m + n + x):= by exact Int.odd_iff.mpr H1
  -- Convert the second condition to show (3m - n + y) is odd
  replace H2 : Odd (3 * m - n + y):= by exact Int.odd_iff.mpr H2
  -- Sum of two odd numbers is even
  have H : Even (5 * m + n + x + (3 * m - n + y)):= by exact Odd.add_odd H1 H2
  -- Lead to contradiction
  absurd H
  -- Simplify the expression
  simp
  -- Rewrite the sum to show it equals 8m + (x + y)
  rw [show 5 * m + n + x + (3 * m - n + y) = 8 * m + (x + y) by omega]
  -- Prove that 8m + (x + y) is odd, which contradicts H
  suffices Even (8 * m) by exact Even.add_odd this h1
  -- Show that 8m is even by expressing it as 2(4m)
  use 4 * m
  ring
