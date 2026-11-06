import Mathlib
/- Compute

$$
100^{2}+99^{2}-98^{2}-97^{2}+96^{2}+95^{2}-94^{2}-93^{2}+\ldots+4^{2}+3^{2}-2^{2}-1^{2}
$$ -/
theorem algebra_609732 : ∑ i in Finset.range 25, (((4 * i + 4) ^ 2 : ℝ) + (4 * i + 3) ^ 2 - (4 * i + 2) ^ 2 - (4 * i + 1) ^ 2) = 10100:= by

  -- Lemma 1: Rewrite the sum by separating the largest square term
  -- This helps simplify the calculation by grouping terms differently
  have h1 : ∀ n : ℕ, ∑ i in Finset.range (n + 1), (((4 * (↑i : ℝ) + 4) ^ 2 : ℝ) + (4 * ↑i + 3) ^ 2 - (4 * ↑i + 2) ^ 2 - (4 * ↑i + 1) ^ 2) = (4 * (↑n : ℝ) + 4) ^ 2 + ∑ i in Finset.range (n + 1), (((4 * (↑i : ℝ) + 3) ^ 2 : ℝ) - (4 * ↑i + 2) ^ 2 - (4 * ↑i + 1) ^ 2 + (4 * ↑i) ^ 2):= by
    intro n
    induction n with
    | zero =>
      simp
      linarith
    | succ n ih =>
      set m:= n + 1 with hm
      clear_value m
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [ih]
      rify at hm
      rw [show 4 * (↑n : ℝ) + 4 = 4 * ↑m by linarith]
      linarith

  -- Lemma 2: Prove that each group of four terms simplifies to 4
  -- This is a key observation that makes the final calculation much simpler
  have h2 : ∀ i ∈ Finset.range 25, (((4 * (↑i : ℝ) + 3) ^ 2 : ℝ) - (4 * ↑i + 2) ^ 2 - (4 * ↑i + 1) ^ 2 + (4 * ↑i) ^ 2) = 4:= by
    intro i _
    linarith

  -- Apply the previous lemma to simplify the sum
  replace h2 : ∑ i in Finset.range 25, (((4 * (↑i : ℝ) + 3) ^ 2 : ℝ) - (4 * ↑i + 2) ^ 2 - (4 * ↑i + 1) ^ 2 + (4 * ↑i) ^ 2) = ∑ i in Finset.range 25, 4:= by exact Finset.sum_congr rfl h2

  -- Apply Lemma 1 with n = 24 (since we want range 25)
  specialize h1 24
  rw [show 24 + 1 = 25 by linarith] at h1
  rw [h1, h2]
  simp
  linarith
