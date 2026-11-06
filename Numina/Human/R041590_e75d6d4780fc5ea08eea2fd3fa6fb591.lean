import Mathlib

/- 8-27 Let the sequence of positive numbers $a_{0}, a_{1}, a_{2}, \cdots$ satisfy $a_{0}=a_{1}=1$ and

$$

\sqrt{a_{n} a_{n-2}}-\sqrt{a_{n-1} a_{n-2}}=2 a_{n-1}, n=2,3, \cdots

$$


Find the general term formula of the sequence. -/
theorem algebra_282633 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h0 : a 0 = 1) (h1 : a 1 = 1)
    (h : ∀ n, 2 ≤ n → √(a n * a (n - 2)) - √(a (n - 1) * a (n - 2)) = 2 * a (n - 1)) :
    ∀ n, a n = ∏ k ∈ Finset.Icc 1 n, (2 ^ k - 1) ^ 2
  := by

    -- recursive description for √(a n)
    have sqrt_eq : ∀ n, 2 ≤ n →
      √(a n) = √(a (n - 1)) + (2 * a (n - 1)) / √(a (n - 2)) := by
      intro n nh
      have orig_eq := h n nh
      rw [Real.sqrt_mul, Real.sqrt_mul] at orig_eq
      convert_to (√(a n) - √(a (n - 1))) * √(a (n - 2)) = 2 * a (n - 1) at orig_eq
      ring
      have not_zero : √(a (n - 2)) ≠ 0 := Real.sqrt_ne_zero'.mpr (ha (n - 2))
      have yeah := eq_div_of_mul_eq not_zero orig_eq
      rw [←yeah]
      ring_nf
      exact le_of_lt (ha (n - 1))
      exact le_of_lt (ha n)

    -- let b n = √(a n / a (n - 1))
    let b : ∀ n : ℕ, 1 ≤ n → ℝ := fun n nh => √((a n) / a (n -1))

    -- then b 1 = 1
    have b_one : b 1 (le_refl 1) = 1 := by
      unfold b
      simp only [h1, tsub_self, h0, ne_eq, one_ne_zero, not_false_eq_true, div_self, Real.sqrt_one]

    -- and b_n = 1 + 2 * b_(n - 1)
    have b_rest : ∀ n : ℕ, (hn : 2 ≤ n)
      → b n (Nat.one_le_of_lt hn) = 1 + 2 * b (n - 1) (Nat.le_sub_one_of_lt hn) := by
        intro n hn
        induction' n, hn using Nat.le_induction with h3 h4 h5
        · unfold b
          simp only [Nat.add_one_sub_one, h1, div_one, sqrt_eq 2 (le_refl 2), Real.sqrt_one,
            mul_one, tsub_self, h0, ne_eq, one_ne_zero, not_false_eq_true, div_self]
        · simp only [add_tsub_cancel_right]
          unfold b
          simp only [add_tsub_cancel_right]
          ring_nf
          rw [Real.sqrt_mul, Real.sqrt_mul]
          have hue := sqrt_eq (1 + h3) (le_add_of_le_right h4)
          rw [hue]
          have : √(a h3) ≠ 0 := Real.sqrt_ne_zero'.mpr (ha h3)
          have eqq : 1 + h3 - 2 = h3 - 1 := by
            omega
          rw [eqq]
          have eqq2 : 1 + h3 - 1 = h3 := by
            omega
          rw [eqq2]
          ring_nf
          field_simp
          rw [mul_comm, mul_div_mul_comm]
          simp only [Real.div_sqrt]
          ring_nf
          exact le_of_lt (ha h3)
          exact le_of_lt (ha (1 + h3))

    -- then b_n = 2 ^ n - 1
    have b_simple : ∀ n, (hn : 1 ≤ n) → b n hn = 2 ^ n - 1 := by
      intro n hn
      induction' n, hn using Nat.le_induction with h3 h4 h5
      · simp only [b_one, pow_one]
        ring
      · rw [b_rest (h3 + 1) (Nat.le_add_of_sub_le h4)]
        simp only [add_tsub_cancel_right, h5]
        ring_nf

    -- then √(a n) = (2 ^ n - 1) * √(a (n - 1))
    have a_simple : ∀ n, (hn : 1 ≤ n) → √(a n) = (2 ^ n - 1) * √(a (n - 1)) := by
      intro n hn
      rw [(b_simple n hn).symm]
      unfold b
      rw [Real.sqrt_div]
      have yeah : √(a (n - 1)) ≠ 0 := Real.sqrt_ne_zero'.mpr (ha (n - 1))
      ring_nf
      field_simp
      exact le_of_lt (ha n)

    intro n
    -- rewrite as equality of √(a n)
    convert_to (√(a n)) ^ 2 = ∏ k ∈ Finset.Icc 1 n, (2 ^ k - 1) ^ 2
    · exact (Real.sq_sqrt <| le_of_lt (ha n)).symm
    rw [Finset.prod_pow]
    apply (pow_left_inj₀ (a n).sqrt_nonneg ?_ (by decide)).mpr
    -- then we can prove the result using induction
    · induction' n with h4 h5
      -- base case n = 0 is clear
      · simp only [h0, Real.sqrt_one, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.prod_empty]
      -- use √(a n) = (2 ^ n - 1) * √(a (n - 1)) and hypothesis to prove induction case
      · have h4_one : 1 ≤ h4 + 1 := (Nat.le_add_left 1 h4)
        rw [a_simple (h4 + 1) h4_one, Finset.prod_Icc_succ_top h4_one, ←h5, add_tsub_cancel_right]
        ring_nf
    -- product is nonnegative so it was fine to remove square
    · apply Finset.prod_nonneg
      simp only [Finset.mem_Icc, sub_nonneg, and_imp]
      intro i i1 i2
      exact (pow_le_pow_iff_right₀ one_lt_two).mpr <| Nat.zero_le i