import Mathlib

/- * Let the general term formula of the sequence be

$$

a_{n}=1+2^{2}+3^{3}+\cdots+n^{n} .

$$


Prove: There are infinitely many odd terms in the sequence. -/
theorem number_theory_113226 (a : ℕ → ℕ)
    (ha : ∀ n, a n = ∑ i in Finset.Icc 1 n, i ^ i) :
    ∀ N, ∃ n, n > N ∧ Odd (a n) := by
    intro n
    -- We'll prove that a (4 * n + 1) will be odd
    refine ⟨4 * n + 1, by omega, ?_⟩

    -- We'll use induction on n
    induction' n with p ph
    -- zero case is obviously true
    · simp only [mul_zero, zero_add, ha 1, Finset.Icc_self,
        Finset.sum_singleton, pow_one, odd_one]
    · rw [ha (4 * (p + 1) + 1)]
      rw [ha (4 * p + 1)] at ph
      -- Split the sum up to make it easier to apply the induction hypothesis
      convert_to Odd (∑ i ∈ Finset.Icc 1 (4 * p + 1 + 1 + 1 + 1 + 1), i ^ i)
      rw [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top,
      Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top]
      convert_to Odd ((∑ k ∈ Finset.Icc 1 (4 * p + 1), k ^ k)
        + ((4 * p + 1 + 1) ^ (4 * p + 1 + 1) + (4 * p + 2 + 1) ^ (4 * p + 2 + 1)
        + (4 * p + 3 + 1) ^ (4 * p + 3 + 1) + (4 * p + 4 + 1) ^ (4 * p + 4 + 1)))
      ring
      -- Apply the induction hypothesis, using odd + even = odd
      refine Odd.add_even ph ?_
      -- Prove that the rest is even by looking at each value at
      -- the end of the sum (four values)
      apply Odd.add_odd
      apply Odd.add_even
      apply Even.add_odd
      · apply Nat.even_pow.mpr
        refine ⟨?_, by positivity⟩
        rw [Nat.even_iff]
        omega
      · rw [←Nat.not_even_iff_odd]
        refine Nat.even_pow.mp.mt <| Classical.not_and_iff_or_not_not.mpr <| Or.inl ?_
        rw [Nat.even_iff]
        omega
      · apply Nat.even_pow.mpr
        refine ⟨?_, by positivity⟩
        rw [Nat.even_iff]
        omega
      · rw [←Nat.not_even_iff_odd]
        refine Nat.even_pow.mp.mt <| Classical.not_and_iff_or_not_not.mpr <| Or.inl ?_
        rw [Nat.even_iff]
        omega
      all_goals
      · omega