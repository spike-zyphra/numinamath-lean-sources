import Mathlib

/-Find the sum: $(-39) + (-37) + \cdots + (-1)$.-/
theorem algebra_10571 : ∑ i ∈ Finset.range 20, (- (2 : ℤ) * i - 1) = -400 := by
  simp only [Int.reduceNeg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_neg,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  -- The sum is an arithmetic series with common difference 2. Let $n$ be the number of terms.
  -- Then the $n$th term is $-1$, so $-39 + (n-1)(2) = -1$, or $n = 20$. The sum of an arithmetic series is equal to the average of the first and last term, multiplied by the number of terms, so the sum is $[(-39) + (-1)]/2 \cdot 20 = \boxed{-400}$.
  have : ∑ i ∈ Finset.range 20, (i : ℤ) = ∑ i ∈ Finset.range 20, i := by simp
  rw [←Finset.mul_sum, this, Finset.sum_range_id 20]
  simp
