import Mathlib
/- Find

$$
\frac{2^{2}}{2^{2}-1} \cdot \frac{3^{2}}{3^{2}-1} \cdot \frac{4^{2}}{4^{2}-1} \cdots \cdots \frac{2006^{2}}{2006^{2}-1}
$$ -/
theorem algebra_611461 : ∏ i ∈ Finset.range 2005, (((i + 2) ^ 2 : ℝ) / ((i + 2) ^ 2 - 1)) = 4012 / 2007:= by

  -- Helper lemma: For any natural number n, prove that the product from 2 to n+2 equals 2(n+2)/(n+3)
  have h : ∀ n : ℕ, ∏ i ∈ Finset.range (n + 1), (((i + 2) ^ 2 : ℝ) / ((i + 2) ^ 2 - 1)) = (2 : ℝ) * (n + 2) / (n + 3):= by
    intro n
    induction n with
    -- Base case: n = 0
    | zero =>
      simp
      norm_num
    -- Inductive step: prove for n+1 assuming it holds for n
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      field_simp
      -- Rewrite the denominator using algebraic manipulation
      rw [show (↑n + 1 + 2) ^ 2 - (1 : ℝ) = (↑n + 2) * (↑n + 4) by linarith]
      -- Establish that n is non-negative
      have hnpos : n ≥ 0:= by linarith
      rify at hnpos
      field_simp
      linarith

  -- Apply the helper lemma with n = 2004
  specialize h 2004
  -- Rewrite 2004 + 1 as 2005
  rw [show 2004 + 1 = 2005 by linarith] at h
  rw [h]
  norm_num
