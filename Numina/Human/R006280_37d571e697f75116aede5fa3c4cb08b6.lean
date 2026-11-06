import Mathlib

/-Let $D$ be an integer such that $2 \le D \le 9$. Let $n$ be a $D$-digit natural number,
written in base 10 as $(d_{D-1} d_{D-2} \ldots d_1 d_0)_{10}$,
where $d_{D-1}$ is the most significant digit. Let $Q(n) = \sum_{i=0}^{D-1} d_i$ be the sum of its digits.
The following conditions must hold: 1.
The digits are strictly decreasing from left to right: $d_{D-1} > d_{D-2} > \ldots > d_1 > d_0$. 2.
For a given positive integer $L$, $n^{Q(n)}$ satisfies $10^L < n^{Q(n)} < 10^{L+1}$.
Consider the case where $D=4$ and $L=98$. Find the unique natural number $n$ that satisfies these conditions.
Show that the answer is $n=8764$.-/

theorem number_theory_635488 (n: ℕ) (h_uniqueness: ∀ n', 1000 ≤ n' ∧ n' < 10000 ∧ n' % 10 < (n' / 10 % 10) ∧
  (n' / 10 % 10) < (n' / 100 % 10) ∧ (n' / 100 % 10) < (n' / 1000) ∧
  10 ^ 98 < n' ^ (Nat.digits 10 n').sum ∧ n' ^ (Nat.digits 10 n').sum < 10 ^ 99 → n' = n): n = 8764 := by

  specialize h_uniqueness 8764
  symm
  apply h_uniqueness
  native_decide