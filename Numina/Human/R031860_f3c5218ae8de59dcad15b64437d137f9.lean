import Mathlib

/- 9. (16 points) Given the sequence $\left\{a_{n}\right\}$ satisfies:

$$
\begin{array}{l}
a_{1}=1, a_{2}=2, a_{3}=4, \\
a_{n}=a_{n-1}+a_{n-2}-a_{n-3}+1(n \geqslant 4) .
\end{array}
$$

(1) Find the general term formula for the sequence $\left\{a_{n}\right\}$;
(2) Prove: $\frac{1}{a_{1}}+\frac{1}{a_{2}}+\cdots+\frac{1}{a_{2016}}<3$. -/

theorem algebra_265201 {a : ℕ → ℤ} (ha0 : a 0 = 0) (ha1 : a 1 = 1) (ha2 : a 2 = 2) (ha3 : a 3 = 4)
    (han : ∀ n ≥ 4, a n = a (n - 1) + a (n - 2) - a (n - 3) + 1) :
    (∀ n, (Even n → a n = (n : ℚ) * (n + 2) / 4) ∧ (Odd n → a n = ((n : ℚ) + 1)^2 / 4)) ∧ (∑ i in Finset.Icc 1 2016, (1 / a i : ℚ) < 3) := by

  -- We will prove the first part of the theorem by induction on n.
  have val_seq (n : ℕ) : (Even n → a n = (n : ℚ) * (n + 2) / 4) ∧ (Odd n → a n = ((n : ℚ) + 1)^2 / 4) := by
    induction' n using Nat.strong_induction_on with n ih
    match n with
      -- Base cases.
      | 0 => simp [ha0]
      | 1 => simp [ha1]; norm_num
      | 2 => simp [ha2]; norm_num
      | 3 => simp [ha3]; norm_num; decide
      -- Inductive step.
      | n+4 =>
        rw [han (n + 4) (Nat.le_add_left 4 n)]
        simp only [Nat.add_one_sub_one, Nat.reduceSubDiff, Int.cast_add, Int.cast_sub, Int.cast_one,
          Nat.cast_add, Nat.cast_ofNat]
        -- We have different formulae for even and odd n, so we should distinguish between the two cases.
        by_cases h : Even n
        · constructor
          -- If n is even, we use the appropriate formula for a n and complete the computation.
          · -- n+4 is even.
            intro h'
            rw [(ih (n + 3) (by simp)).2 (Even.add_odd h (by decide))]
            rw [(ih (n + 2) (by simp)).1 (Even.add h (by decide))]
            rw [(ih (n + 1) (by simp)).2 (Even.add_one h)]
            field_simp
            ring
          · -- In this case, n+4 cannot be odd, so we have a contradiction.
            intro h'
            simp only [add_comm n 4, Nat.odd_add, h, iff_true] at h'
            contradiction
        · -- If n is odd, we use the appropriate formula for a n and complete the computation.
          constructor
          · -- In this case, n+4 cannot be even, so we have a contradiction.
            intro h'
            simp only [Nat.even_add, h, false_iff, Nat.not_even_iff_odd] at h'
            contradiction
          · -- n+4 is odd.
            intro h'
            rw [Nat.not_even_iff_odd] at h
            rw [(ih (n + 3) (by simp)).1 (Odd.add_odd h (by decide))]
            rw [(ih (n + 2) (by simp)).2 (Odd.add_even h (by decide))]
            rw [(ih (n + 1) (by simp)).1 (Odd.add_one h)]
            field_simp
            ring

  refine ⟨val_seq, ?_⟩

  -- For the second part of the theorem, we prove by induction that the sum of the reciprocals of the
  -- first n terms of the sequence is less than 3 - (2 / (n + 1) + 2 / (n + 2)).
  have (n : ℕ) : ∑ i in Finset.Icc 1 n, (1 / a i : ℚ) <= 3 - (2 / (n + 1) + 2 / (n + 2)) := by
    induction' n with n ih
    · simp; linarith
    · rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]
      rw [← le_sub_iff_add_le]
      apply le_trans ih
      rw [sub_sub, sub_le_sub_iff_left, ← le_sub_iff_add_le']

      -- The reciprocal of a n+1 is less than 2 / (n + 1) - 2 / (n + 3).
      have : ((1 : ℚ) / (a (n + 1))) ≤ (2 / (n + 1) - 2 / (n + 3)) := by
        -- We prove this using the formula for a n+1, which depends on whether n+1 is even or odd.
        by_cases h : Even (n + 1)
        · rw [(val_seq (n + 1)).1 h]
          apply le_of_eq
          field_simp
          ring
        · rw [(val_seq (n + 1)).2 (Nat.not_even_iff_odd.mp h)]
          field_simp
          ring_nf
          rw [mul_le_mul_iff_of_pos_right (by decide), inv_le_inv₀ (by positivity) (by positivity)]
          linarith
      -- The thesis follows.
      exact le_trans this (le_of_eq (by field_simp; ring))
  -- The inequality follows by transitivity from the previous results.
  exact lt_of_le_of_lt (this 2016) (by linarith)