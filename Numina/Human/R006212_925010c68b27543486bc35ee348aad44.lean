import Mathlib
/- Let $M$ be a positive integer and $K$ be an integer. Determine the sum of the $M$ integers $x_j = j-K$ where $j$ takes values from $0$ to $M-1$. Show the answer is $\frac{M(M-1-2K)}{2}$. -/
theorem number_theory_634695 (M : ℕ) (hM : M > 0) : ∑ i in Finset.range M, ((i : ℝ) - K) = M * (M - 1 - 2 * K) / 2:= by
  -- Prove by induction that the formula holds for all natural numbers n
  have h1 : ∀ n : ℕ, ∑ i in Finset.range n, ((i : ℝ) - K) = n * (n - 1 - 2 * K) / 2:= by
    intro n
    -- Use induction on n
    induction n with
    -- Base case: when n = 0
    | zero =>
      simp
    -- Inductive step: prove for n + 1 assuming it holds for n
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp
      linarith
  -- Apply the proven result to M
  exact h1 M
