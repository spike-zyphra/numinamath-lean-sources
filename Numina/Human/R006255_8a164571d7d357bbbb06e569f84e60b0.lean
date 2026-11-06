import Mathlib

/-
Let $K$ be an integer. A four-digit number $n$ has the property that the sum of $n$ and the sum of its digits is $K$. If $K=2000$, show that $n=1981$.
-/

theorem number_theory_635190 (K:ℕ) (hK: K = 2000) (n a b c d:ℕ)
(hn: n = 1000 * a + 100 * b + 10 * c + d)
(al: 1≤ a) (au: a ≤ 9)
(bu: b ≤ 9)
(cu: c ≤ 9)
(du: d ≤ 9)
(h: n + a + b + c +d = K):
n = 1981 := by

  omega