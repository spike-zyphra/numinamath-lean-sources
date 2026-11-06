import Mathlib

-- Suppose that |x_i| < 1 for i = 1, 2, …, n. Suppose further that |x_1| + |x_2| + ⋯ + |x_n| = 19 + |x_1 + x_2 + ⋯ + x_n|. What is the smallest possible value of n?

theorem algebra_95331 : IsLeast {n : ℕ | ∃ (x : Fin n → ℝ), (∀ i, |x i| < 1) ∧
    (∑ i, |x i| = 19 + |∑ i, x i|)} 20 := by
  constructor
  -- We show that 20 is a lower bound
  · rw [Set.mem_setOf_eq]
    -- We use the function that gives 19/20 on the first 10 elements and -19/20 on the next 10
    use (λ i ↦ if i.val < 10 then ((19 : ℝ)/20) else (-(19 : ℝ)/20))
    constructor
    · intro i
      split_ifs
      · rw [abs_of_nonneg] <;> linarith
      · rw [abs_of_nonpos] <;> linarith
    · -- The absolute value is 19/20 regardless of the element
      have (i : Fin 20) : |(λ (i : (Fin 20)) ↦ if i.val < 10 then ((19 : ℝ)/20)
          else (-(19 : ℝ)/20)) i| = (19 : ℝ)/20 := by
        dsimp
        split_ifs
        · rw [abs_of_nonneg]; linarith
        · rw [abs_of_nonpos] <;> linarith
      -- The LHS is 19
      simp_rw [this]
      simp only [Nat.reduceAdd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]
      ring_nf ; symm
      -- The sum must be zero. We split it in two parts, x < 10 and x ≥ 10.
      rw [add_right_eq_self, abs_eq_zero, Finset.sum_fin_eq_sum_range, (by linarith : 20 = 10 + 10),
        Finset.sum_range_add, ← eq_neg_iff_add_eq_zero]
      nth_rw 2 [neg_eq_neg_one_mul]
      rw [Finset.mul_sum]
      simp only [Nat.reduceAdd, add_lt_iff_neg_left, not_lt_zero', ↓reduceIte, dite_eq_ite, mul_ite,
        neg_mul, one_mul, mul_zero]
      -- The two parts are opposite of each other
      apply Finset.sum_congr (by rfl)
      intro x hx
      rw [Finset.mem_range] at hx
      split_ifs <;> linarith
  -- We show that 20 is the minimum value
  · intro n hn
    rw [Set.mem_setOf_eq] at hn
    obtain ⟨x, hx1, hx2⟩ := hn
    by_cases h : n = 0
    -- n must be strictly positive
    · subst h
      simp_all only [IsEmpty.forall_iff, Finset.univ_eq_empty, Finset.sum_empty, abs_zero, add_zero,
      OfNat.zero_ne_ofNat]
    -- There must be at least 20 terms for the sum to be greater than 19
    · rw [Nat.succ_le_iff]
      rify
      apply lt_of_le_of_lt (le_add_of_nonneg_right (by simp : 0 ≤ |∑ i : Fin n, x i|))
      rw [← hx2, ← mul_one (n : ℝ), ← nsmul_eq_mul, ← Fin.sum_const]
      apply Finset.sum_lt_sum (by intro i _; exact le_of_lt (hx1 i))
      use ⟨0, Nat.zero_lt_of_ne_zero h⟩
      simp only [Finset.mem_univ, true_and]
      exact hx1 ⟨0, Nat.zero_lt_of_ne_zero h⟩