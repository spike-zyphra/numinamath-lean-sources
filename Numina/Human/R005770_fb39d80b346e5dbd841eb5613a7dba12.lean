import Mathlib

/- FInd the value of

$$
\sum_{k=1}^{60} \sum_{n=1}^{k} \frac{n^{2}}{61-2 n}
$$-/
theorem algebra_609820 : ∑ k ∈ Finset.Icc 1 (60 : ℕ), ∑ n ∈ (Finset.Icc 1 k), (n ^ 2 / (61 - 2 * n : ℚ)) = -18910 := by
  -- We do a series of steps to evaluate the sum.
  calc
    _ = ∑ k ∈ Finset.Icc 1 (60 : ℕ), ∑ n ∈ Finset.Icc 1 (60 : ℕ), if n ∈ Finset.Icc 1 k then n ^ 2 / (61 - 2 * n : ℚ) else 0 := by
      -- Change both summations to the same range [1, 60].
      rw [Finset.sum_congr]
      . rfl
      . intro k hk
        simp at hk
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_congr]
        . ext n
          simp
          omega
        . simp
    _ = ∑ n ∈ Finset.Icc 1 (60 : ℕ), ∑ k ∈ Finset.Icc 1 (60 : ℕ), if n ∈ Finset.Icc 1 k then n ^ 2 / (61 - 2 * n : ℚ) else 0 := by
      -- Swap the summations.
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 (60 : ℕ), n ^ 2 / (61 - 2 * n : ℚ) * ∑ k ∈ Finset.Icc n (60 : ℕ), 1 := by
      -- Simplify the expression after moving n out.
      rw [Finset.sum_congr]
      . rfl
      . intro n hn
        simp at hn
        rw [Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_congr]
        . ext k
          simp
          omega
        . simp
    _ = ∑ n ∈ Finset.Icc 1 (60 : ℕ), n ^ 2 / (61 - 2 * n : ℚ) * (60 + 1 - n) := by
      -- The inner summation is simplified because the terms are constant. 
      rw [Finset.sum_congr]
      . rfl
      . intro n hn
        simp at hn
        rw [Finset.sum_const, Nat.card_Icc]
        simp
        norm_cast
        rw [Int.natCast_sub, Int.subNatNat_eq_coe]
        simp
        omega
    _ = -18910 := by
      -- The final step is by calculation.
      norm_num [Finset.sum_Icc_succ_top]