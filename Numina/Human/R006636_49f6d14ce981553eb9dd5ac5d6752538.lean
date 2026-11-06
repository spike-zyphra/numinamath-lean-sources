import Mathlib
/- Let $N$ be a positive natural number. Show that the sum of all odd natural numbers $x$ such that $1 \le x \le N$ is equal to $\left(\left\lfloor \frac{N+1}{2} \right\rfloor\right)^2$. -/
theorem number_theory_639500 (N : ℕ) (hN : N > 0) : ∑ i in Finset.range ((N + 1) / 2), (2 * i + 1) = ((N + 1) / 2) ^ 2:= by
  -- Helper lemma: For any natural number k, the sum of first k odd numbers equals k²
  have h1 : ∀ k : ℕ, ∑ i in Finset.range k, (2 * i + 1) = k ^ 2:= by
    intro k
    -- Proof by induction on k
    induction k with
    -- Base case: when k = 0
    | zero =>
      simp
    -- Inductive step: prove for k + 1 assuming it holds for k
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  -- Apply the helper lemma with k = (N+1)/2 to prove the main theorem
  exact h1 ((N + 1) / 2)
