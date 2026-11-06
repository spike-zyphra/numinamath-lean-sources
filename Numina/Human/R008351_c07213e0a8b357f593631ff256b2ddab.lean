import Mathlib

/- Let $x$ and $y$ be complex numbers such that $|x|=|y|=1$.
(a) [15] Determine the maximum value of $|1+x|+|1+y|-|1+x y|$.
(b) [15] Determine the maximum value of $|1+x|+|1+x y|+\left|1+x y^{2}\right|+\ldots+\left|1+x y^{2011}\right|-1006|1+y|$. -/
theorem algebra_608881:
  ( IsGreatest {u:ℝ | ∃ (x y:ℂ), ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
    u = ‖1+x‖ + ‖1+y‖ - ‖1+x*y‖} (2*√2) )    ∧
  ( IsGreatest {u:ℝ | ∃ (x y:ℂ), ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
    u = (∑ i ∈ Finset.range 2012, ‖1 + x*y^i‖) - 1006*‖1+y‖} (2012*√2) ) := by


  -- ‖1+a‖ + ‖1-a‖ ≤ 2√(‖1-a^2‖)
  have ineq {a:ℂ} (ha: ‖a‖ ≤ 1): ‖1+a‖ + ‖1-a‖ ≤ 2 * √2 := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    -- a.re^2 + a.im^2 = 1
    replace ha: a.re*a.re + a.im*a.im ≤ 1 := by
      have: ‖a‖^2 ≤ 1 := by
        exact (sq_le_one_iff₀ (norm_nonneg _)).mpr ha
      rw [← real_inner_self_eq_norm_sq a] at this
      simp only [Complex.inner, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, neg_mul, sub_neg_eq_add] at this
      exact this
    have are_abs_le: |a.re| ≤ 1 := by
      refine (sq_le_one_iff_abs_le_one a.re).mp ?_
      linarith only [sq_nonneg a.im, ha]
    rw [abs_le] at are_abs_le
    -- let a = a.re + a.im, then (1+a) conj(1+a) =
    --  (1+a.re + a.im) (1+a.re - a.im) = 2 + 2 a.re
    have h1: inner (1+a) (1+a) ≤ 2 + 2 * a.re := by
      simp only [Complex.inner, map_add, map_one, Complex.mul_re, Complex.add_re, Complex.one_re,
        Complex.conj_re, Complex.add_im, Complex.one_im, Complex.conj_im, zero_add, neg_mul,
        sub_neg_eq_add]
      linarith only [ha]
    -- similarly, (1-a) conj(1-a) = 2 - 2 a.re
    have h2: inner (1-a) (1-a) ≤ 2 - 2 * a.re := by
      simp only [Complex.inner, map_sub, map_one, Complex.mul_re, Complex.sub_re, Complex.one_re,
        Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im, sub_neg_eq_add, zero_add,
        zero_sub, mul_neg]
      linarith only [ha]
    -- take square
    have h3: (√(2+2*a.re) + √(2-2*a.re))^2 = 4 + √(4 - 4 * a.re^2) * 2 := by
      have nng1: 0 ≤ 2 + a.re*2 := by
        linarith only [are_abs_le.left]
      have nng2: 0 ≤ 2 - a.re*2 := by
        linarith only [are_abs_le.right]
      ring_nf
      rw [Real.sq_sqrt nng1, Real.sq_sqrt nng2,
      ← Real.sqrt_mul nng1, ← sq_sub_sq]
      ring_nf
    -- √(4 - ..) x 2 ≤ 2 x 2 = 4.
    have h4: √(4 - 4*a.re^2) * 2 ≤ 4 := by
      have hh1: √(4 - 4*a.re^2) ≤ √4 := by
        apply Real.sqrt_le_sqrt (by linarith only [sq_nonneg a.re])
      have hh2: √(4:ℝ) = 2 := by
        have: (4:ℝ) = 2^2 := by norm_num
        rw [this, Real.sqrt_sq (by norm_num)]
      linarith only [hh1, hh2]
    have h5: 2*√2 = √(8:ℝ) := by
      have: (8:ℝ) = 2^2 * 2 := by norm_num
      rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have h6: √(inner (1+a) (1+a)) + √(inner (1-a) (1-a)) ≤
      √(2+2*a.re) + √(2-2*a.re) := by
      apply add_le_add
      all_goals apply Real.sqrt_le_sqrt (by assumption)
    apply le_trans h6 ?_
    replace h3: (√(2+2*a.re) + √(2-2*a.re))^2 ≤ (2*√2)^2 := by
      rw [h5, Real.sq_sqrt (by norm_num), h3]
      linarith only [h4]
    rwa [sq_le_sq₀ (by positivity) (by positivity)] at h3

  -- |1+i| = √2
  have norm_one_add_i: ‖1+Complex.I‖ = √2 := by
    rw [norm_eq_sqrt_real_inner]
    simp only [Complex.inner, map_add, map_one, Complex.conj_I, Complex.mul_re, Complex.add_re,
      Complex.one_re, Complex.neg_re, Complex.I_re, neg_zero, add_zero, mul_one, Complex.add_im,
      Complex.one_im, Complex.neg_im, Complex.I_im, zero_add, sub_neg_eq_add, nonneg_add_self_iff,
      zero_le_one, Nat.ofNat_nonneg, Real.sqrt_inj]
    ring

  -- |1-i| = √2
  have norm_one_sub_i: ‖1 + -Complex.I‖ = √2 := by
    rw [norm_eq_sqrt_real_inner]
    simp only [Complex.inner, map_add, map_one, map_neg, Complex.conj_I, neg_neg, Complex.mul_re,
      Complex.add_re, Complex.one_re, Complex.I_re, add_zero, Complex.neg_re, neg_zero, mul_one,
      Complex.add_im, Complex.one_im, Complex.I_im, zero_add, Complex.neg_im, mul_neg,
      sub_neg_eq_add, nonneg_add_self_iff, zero_le_one, Nat.ofNat_nonneg, Real.sqrt_inj]
    ring

  -- back to the problem.
  constructor
  · -- first part of the problem. max of |1+x| + |1+y| + |1+xy| is 2√2
    rw [IsGreatest, upperBounds]
    simp only [exists_and_left, Set.mem_setOf_eq,
    forall_exists_index, and_imp]
    constructor
    · -- reach maximum when x=y=i.
      use Complex.I
      refine ⟨(by simp), ?_⟩
      use Complex.I
      refine ⟨(by simp), ?_⟩
      simp only [mul_neg, Complex.I_mul_I, neg_neg,
      norm_one_add_i, two_mul, add_neg_cancel, norm_zero, sub_zero]
    · rintro _ x hx y hy rfl
      have h1 := norm_sub_norm_le (1+y) (1+x*y)
      have h2: ‖1+y - (1+x*y)‖ ≤ ‖y‖ * ‖1-x‖ := by
        have: 1+y-(1+x*y) = y * (1-x) := by ring
        rw [this]
        exact norm_mul_le y (1 - x)
      rw [hy, one_mul] at h2
      have h3: ‖1+x‖ + ‖1-x‖ ≤ 2*√2 := ineq (le_of_eq hx)
      apply le_trans ?_ h3
      linarith only [h1, h2]


  · -- second part of the problem
    rw [IsGreatest, upperBounds]
    simp only [exists_and_left, Set.mem_setOf_eq,
    forall_exists_index, and_imp]
    constructor
    · -- take x = i, y = -1, reach maximum.
      use Complex.I
      refine ⟨(by simp), ?_⟩
      use -1
      refine ⟨(by simp), ?_⟩
      simp only [add_neg_cancel, norm_zero, mul_zero, sub_zero]
      have: (2012:ℝ) * √2 = ∑ i ∈ Finset.range 2012, √2 := by simp
      rw [this]
      apply Finset.sum_congr rfl ?_
      intro i _
      by_cases hi: Even i
      · simp only [hi, Even.neg_pow, one_pow, mul_one, norm_one_add_i]
      · rw [Nat.not_even_iff_odd] at hi
        simp only [hi, Odd.neg_one_pow, mul_neg, mul_one, norm_one_sub_i]
    ·
      rintro _ x hx y hy rfl
      -- rearrange those sum terms, bundle |1+xy^2k| + |1+xy^(2k+1)|-|1+y| together.
      have h1 (k:ℕ): ∑ i ∈ Finset.range (2*k), ‖1 + x*y^i‖ - k*‖1+y‖ =
        ∑ i ∈ Finset.range k,(‖1+x*y^(2*i)‖ + ‖1+x*y^(2*i+1)‖ - ‖1+y‖) := by
        induction' k with k ih
        · simp
        · have: 2 * (k+1) = 2*k + 1 + 1 := by ring
          simp only [this, Finset.sum_range_succ]
          rw [← ih]
          push_cast
          ring

      -- thus it ≤ |1+xy^2k| + |1-xy^2k|
      have h2 {i:ℕ}: ‖1+x*y^(2*i)‖ + ‖1+x*y^(2*i+1)‖ - ‖1+y‖ ≤
        ‖1+x*y^(2*i)‖ + ‖1-x*y^(2*i)‖ := by
        have hh1: ‖1+x*y^(2*i+1)‖ - ‖1+y‖ ≤ ‖x*y^(2*i+1) - y‖ := by
          apply le_trans (norm_sub_norm_le _ _) (le_of_eq ?_)
          congr 1; ring
        have hh2: ‖x*y^(2*i+1) - y‖ ≤ ‖1 - x*y^(2*i)‖ := by
          rw [pow_succ, ← mul_assoc, ← sub_one_mul, norm_sub_rev]
          apply le_trans (norm_mul_le _ _) (le_of_eq ?_)
          rw [hy, mul_one]
        linarith only [hh1, hh2]

      -- |1+xy^2k| + |1-xy^2k| ≤ 2√2
      have h3 {i:ℕ}:  ‖1+x*y^(2*i)‖ + ‖1-x*y^(2*i)‖ ≤ 2*√2 := by
        apply ineq
        apply le_trans (norm_mul_le _ _) ?_
        rw [hx, norm_pow, hy]
        simp

      have: 2012 = 2*1006 := by ring
      specialize h1 1006
      norm_cast at h1
      rw [this, h1]

      have h4: ∑ i ∈ Finset.range 1006,
        (‖1+x*y^(2*i)‖ + ‖1+x*y^(2*i+1)‖ - ‖1+y‖) ≤
        ∑ i ∈ Finset.range 1006, (2*√2) := by
        apply Finset.sum_le_sum ?_
        intro _ _
        apply le_trans h2 h3

      apply le_trans h4 (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Nat.cast_ofNat]
      ring
