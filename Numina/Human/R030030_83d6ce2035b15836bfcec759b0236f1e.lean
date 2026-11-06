import Mathlib
/- 10. The common difference of an arithmetic sequence with real terms is 4, and the square of the first term plus the sum of the remaining terms does not exceed 100. Such a sequence can have at most $\qquad$ terms. -/
theorem algebra_167304 : IsGreatest {n : ℕ | ∃ a : ℕ → ℝ, (∀ i ∈ Finset.range n, a i = a 0 + 4 * i) ∧ a 0 ^ 2 - a 0 + ∑ i in Finset.range n, a i ≤ 100} 8:= by
  constructor
  -- First part: Prove that n=8 is in the set (i.e., there exists a sequence with 8 terms satisfying the conditions)
  .
    simp
    -- Define a sequence with first term -7/2 and common difference 4
    use (fun n => (-7 / 2 + 4 * n))
    constructor
    -- Verify that the sequence has common difference 4
    .
      intro i _
      simp
    -- Verify that the sum condition is satisfied for n=8
    .
      repeat rw [Finset.sum_range_succ]
      simp
      norm_num
  -- Second part: Prove that n=8 is an upper bound (i.e., no larger value can satisfy the conditions)
  .
    simp [upperBounds]
    intro n a h1 h2
    -- Derive a formula for the sum of the first k terms of the arithmetic sequence
    have h3 : ∀ k : ℕ, k ≤ n → ∑ i ∈ Finset.range k, a i = k * a 0 + 2 * k * (k - 1):= by
      intro k hk
      induction k with
      -- Base case: sum of 0 terms is 0
      | zero =>
        simp
      -- Inductive step: sum of k+1 terms equals sum of k terms plus the (k+1)th term
      | succ k ih =>
        rw [Finset.sum_range_succ, ih (by omega), h1 k (by omega)]
        simp
        linarith
    -- Apply the formula to the full sequence of n terms
    specialize h3 n (by omega)
    rw [h3] at h2
    -- Rewrite the inequality in a form that's easier to analyze
    rw [show a 0 ^ 2 - a 0 + (↑n * a 0 + 2 * ↑n * (↑n - 1)) = (a 0 + (n - 1) / 2) ^ 2 + 7 / 4 * n ^ 2 - 3 / 2 * n - 1 / 4 by linarith] at h2
    -- Note that the square term is non-negative
    have h4 : (a 0 + (↑n - 1) / 2) ^ 2 ≥ 0:= by positivity
    -- Simplify the inequality by removing the non-negative square term
    replace h2 : 7 / 4 * (↑n : ℝ) ^ 2 - 3 / 2 * n - 1 / 4 ≤ 100:= by linarith
    -- Further simplify to an inequality with integer coefficients
    replace h2 : 7 * n ^ 2 ≤ 6 * n + 401:= by rify ; linarith
    -- Proof by contradiction: assume n ≥ 9
    by_contra H
    simp at H
    replace H : n ≥ 9:= by omega
    clear h1 h3 h4 a
    -- Show that the inequality is violated when n ≥ 9, proving that n must be at most 8
    nlinarith
