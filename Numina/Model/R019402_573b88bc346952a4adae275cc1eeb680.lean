import Mathlib

def S (n : ℕ) := ∑ i ∈ Finset.range n, (i * 10 + 9)

theorem algebra_247343 :
    IsLeast {n | 10^5 < S n} 142 := by
  constructor
  · -- We verify that $142 \in \{n | 10^5 < S n\}$.
    show 10^5 < S 142
    norm_num [S, Finset.sum_range_succ]
  · -- For any $n \in \{n | 10^5 < S n\}$, we have $142 \leq n$.
    intro n hn
    have h1 : 10 ^ 5 < S n := by
      simpa using hn
    by_contra h
    push_neg at h
    -- We need to show that if $n < 142$, then $S_n \leq 10^5$.
    have h2 : n ≤ 141 := by linarith
    interval_cases n <;> norm_num [S, Finset.sum_range_succ] at h1 ⊢