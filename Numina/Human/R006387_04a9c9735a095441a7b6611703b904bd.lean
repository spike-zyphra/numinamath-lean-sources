import Mathlib

/- Let $W_0$ be a positive integer. Suppose the total number of students $n$ satisfies the conditions that $n \pmod 4 = 2$ and $n \pmod 5 = 1$.
It is known that $W_0$ students are women. Furthermore, there are more women than men, and the total number of students $n$ is strictly greater than $W_0$.
If $W_0 = 22$, show that the number of male students is 4. -/
theorem number_theory_636551
  (W0 : ℕ)
  (hW0 : W0 > 0)
  (n : ℕ)
  (hn : n % 4 = 2 ∧ n % 5 = 1)
  (hW1 : W0 < n)
  (hW2 : n - W0 < W0)
  (hW3 : W0 = 22)
  : n - W0 = 4 :=
by
  subst hW3
  simp at *
  clear hW0
  have : n < 44 := by omega
  omega
