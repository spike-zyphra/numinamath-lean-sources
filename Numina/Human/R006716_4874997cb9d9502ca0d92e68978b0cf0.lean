import Mathlib

/-Let $M$ be an integer equal to 10. Let $S_M$ be the set of integers $x$
such that $x > M$ and $x$ is a divisor of $M!$.
Let $x_0, x_1, x_2, x_3, x_4$ be the five smallest elements of $S_M$, when elements are taken in increasing order.
Show that the sum $x_0+x_1+x_2+x_3+x_4$ is equal to 75.-/

theorem number_theory_640462 (M: ℕ) (S_M: Finset ℕ) (hM: M = 10)
(hS: S_M = (Nat.divisors (Nat.factorial M)).filter (fun x => x > M)): (((S_M).sort (· ≤ ·)).take 5).sum = 75 := by

   rw [hM] at hS
   rw [hS]
   native_decide