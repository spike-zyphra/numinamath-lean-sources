import Mathlib

/-"Let $K_0$ and $L_0$ be natural numbers.
We are interested in whether the equation $\binom{n}{k}=m^l$ has solutions in natural numbers $n, k, m, l$
subject to $l \ge L_0$ and $K_0 \le k \le n-K_0$.
Show that if $K_0=2$ and $L_0=2$, then such solutions exist.
Specifically, show that the tuple $(n,k,m,l) = (50,2,35,2)$ satisfies these conditions:
$l \ge 2$, $2 \le k \le n-2$, and $\binom{n}{k}=m^l$."
-/

theorem number_theory_635878 (n k m l: ℕ) (h1: n = 50) (h2: k = 2) (h3: m = 35) (h4: l = 2):
  2 ≤ l ∧ 2 ≤ k ∧ k ≤ n - 2 ∧ (n.choose k = m ^ l) := by
  rw [h1, h2, h3, h4]
  native_decide
