import Mathlib

/-Let $k$ be a natural number such that $1 \le k \le 9$.
Let $c_k$ be the number defined by the sum $c_k = \sum_{i=0}^{k-1} 10^i$.
(This means $c_k$ is the integer consisting of $k$ digits, all equal to 1).
Show that $(c_k)^2$ is the integer whose decimal representation
consists of the sequence of digits $1, 2, \ldots, k-1, k, k-1, \ldots, 2, 1$.
For example, for $k=3$, $c_3=111$ and $(c_3)^2 = 12321$.
-/

theorem number_theory_640039 (k c: ℕ) (h1: 1 ≤ k) (h2: k ≤ 9) (h3: c = ∑ i ∈ Finset.range k, 10 ^ i):
  c ^ 2 = (∑ i ∈ Finset.range k, (i + 1) * 10 ^ i) + (∑ j ∈ Finset.range (k - 1), (j + 1) * 10 ^ (2 * k - 2 - j)) := by

    interval_cases k
    all_goals simp [h3, Finset.sum_range_succ]