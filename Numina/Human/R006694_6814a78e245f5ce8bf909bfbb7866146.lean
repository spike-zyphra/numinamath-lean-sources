import Mathlib

/-E907 Let $r$ be an integer satisfying $0 \le r < 3$.
Suppose Natasha has $n$ dimes, where $n$ is an integer such that $10 < n < 100$.
When she arranges the dimes in stacks of 3, $r$ dimes remain.
When she arranges them in stacks of 4, $r$ dimes remain.
Similarly, when she arranges them in stacks of 5, $r$ dimes remain. Show that Natasha has $60+r$ dimes.-/

theorem number_theory_640249 (n r: ℕ) (hr: r < 3) (h1: 10 < n ∧ n < 100) (h2: n % 3 = r) (h3: n % 4 = r) (h4: n % 5 = r):
  n = 60 + r := by

  omega