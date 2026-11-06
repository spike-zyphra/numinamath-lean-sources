import Mathlib
/- Let $N$ be a positive integer. An arithmetic sequence is defined by $a_k = 3+4k$ for $k \ge 0$. Calculate the sum of the first $N$ terms of this sequence (namely, $a_0, a_1, \ldots, a_{N-1}$). Show that this sum is $N(2N+1)$. -/
theorem number_theory_637674 (a : ℕ → ℕ) (ha : a = fun k => 3 + 4 * k) (N : ℕ) (hN : N > 0) : ∑ i in Finset.range N, a i = N * (2 * N + 1):= by
  -- Simplify the goal using the definition of function a
  simp [ha]

  -- Prove by induction that for all natural numbers n,
  -- the sum of (3 + 4k) from k = 0 to n-1 equals n(2n + 1)
  have h1 : ∀ n : ℕ, ∑ k ∈ Finset.range n, (3 + 4 * k) = n * (2 * n + 1):= by
    intro n
    induction n with
    -- Base case: when n = 0
    | zero =>
      simp
    -- Inductive step: prove for n + 1 using the induction hypothesis
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

  -- Apply the proven result to N
  exact h1 N
