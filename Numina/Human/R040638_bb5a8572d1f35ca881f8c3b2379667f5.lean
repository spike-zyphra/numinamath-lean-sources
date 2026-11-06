import Mathlib

/- 7. Given the sequence $a_{1}=3, a_{n+1}=\left(a_{n}-1\right)^{2}+1$, prove: $\prod_{k=1}^{n} a_{k}<2^{2^{n}}$. -/
theorem algebra_108556 (a : ℕ → ℕ) (ha1 : a 1 = 3)
    (han : ∀ n, a (n + 1) = (a n - 1) ^ 2 + 1) (n : ℕ) :
    ∏ k in Finset.Icc 1 n, a k < 2 ^ (2 ^ n)
  := by
    -- a (n + 1) - 1 = 2 ^ (2 ^ n)
    have a_pred_eq : ∀ n, a (n + 1) - 1 = 2 ^ (2 ^ n) := by
      intro n
      induction' n with h1 h2
      · simp only [zero_add, pow_zero, pow_one, Nat.pred_eq_succ_iff, Nat.reduceAdd]
        exact ha1
      · rw [han (h1 + 1), h2, add_tsub_cancel_right]
        ring
    -- so a (n + 1) = 2 ^ (2 ^ n) + 1
    have a_eq : ∀ n, a (n + 1) = 2 ^ (2 ^ n) + 1 := by
      -- reorder
      intro n
      have curr := a_pred_eq n
      rw [←curr]
      refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
      -- valid because 1 ≤ a (n + 1)
      -- proof by contradiction, assume a (n + 1) = 0
      by_contra eq_zero
      simp only [not_le, Nat.lt_one_iff] at eq_zero

      -- but then 2 ^ 2 ^ n = 0, which is impossible
      simpa only [eq_zero, zero_le, Nat.sub_eq_zero_of_le, ne_eq, pow_eq_zero_iff',
        OfNat.ofNat_ne_zero, false_and, not_false_eq_true, pow_eq_zero_iff] using curr.symm

    -- replace a n in sum
    convert_to ∏ k ∈ Finset.Icc 1 n, (2 ^ 2 ^ (k - 1) + 1) < 2 ^ 2 ^ n
    -- all terms are equal
    · apply Finset.prod_congr rfl
      intro aa bb
      -- every k is at least 1
      simp only [Finset.mem_Icc] at bb
      obtain ⟨k', kh⟩ : ∃ u, u + 1 = aa := Nat.exists_add_one_eq.mpr bb.1
      -- apply our equality for a (n + 1)
      rw [←kh, a_eq, add_tsub_cancel_right]
    -- simplify product
    convert_to 2 ^ (2 ^ n) - 1 < 2 ^ 2 ^ n
    -- proof by induction on n
    · induction' n with h1 h2
      -- base case in an empty product
      · simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.prod_empty, pow_zero, pow_one,
          Nat.add_one_sub_one]
      -- split product to apply induction hypothesis
      · rw [Finset.prod_Icc_succ_top, h2, add_tsub_cancel_right,
          mul_comm, ←Nat.sq_sub_sq, one_pow]
        -- rewrite powers
        · congr 1
          ring
        -- 1 ≤ h1 + 1
        · omega
    -- x - 1 < x iff x ≠ 0
    refine Nat.sub_one_lt ?_
    positivity