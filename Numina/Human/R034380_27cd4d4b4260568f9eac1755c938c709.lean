import Mathlib

open Finset

/- Let $n \geq 2$ be some fixed positive integer and suppose that $a_{1}, a_{2}, \ldots, a_{n}$ are positive real numbers satisfying $a_{1}+a_{2}+\cdots+a_{n}=2^{n}-1$.

Find the minimum possible value of

$$
\frac{a_{1}}{1}+\frac{a_{2}}{1+a_{1}}+\frac{a_{3}}{1+a_{1}+a_{2}}+\cdots+\frac{a_{n}}{1+a_{1}+a_{2}+\cdots+a_{n-1}} .
$$ -/
theorem inequalities_604423 {n : ℕ} (hn : 2 ≤ n) :
    IsLeast {∑ i ∈ range n, a i / (1 + (∑ j ∈ range i, a j)) |
      (a : ℕ → ℝ) (_ : ∀ i ∈ range n, 0 < a i)
        (_ : ∑ i ∈ range n, a i = 2 ^ n - 1)} n := by
  have nposr: (0:ℝ) < n := by
    rify at hn
    linarith only [hn]
  have nge1: n ≥ 1 := by linarith only [hn]
  rw [IsLeast, lowerBounds]
  constructor

  · -- prove existence.
    simp only [exists_prop, exists_and_left, Set.mem_setOf_eq]
    -- by later discussion, AM-GM inequality take equal sign when a0=a1=...=a_{n-1}
    -- or, a_k = 2^(k-1) with subscript begin from 1, a_k = 2^k with subscript begin from 0.
    use (fun i => 2^(i:ℕ))
    simp only [Nat.ofNat_pos, pow_pos, implies_true, true_and]
    -- 1+2+4+...+2^(n-1) = 2^n - 1
    have sum_two_pow (m:ℕ): ∑ i ∈ range m, (2:ℝ)^(i:ℕ) = 2^m - 1 := by
      rw [geom_sum_eq (by norm_num)]
      norm_num
    have asum1: ∑ i ∈ range n, (2:ℝ)^(i:ℕ) = 2^n - 1 := sum_two_pow n
    have asum2: ∑ i ∈ range n, ( (2:ℝ)^(i:ℕ) /
      (1 + ∑ j ∈ range i, (2:ℝ)^(j:ℕ)) ) = n := by
      have: (n:ℝ) = ∑ i ∈ range n, 1 := by simp
      rw [this]
      congr 1; funext i
      rw [sum_two_pow i]
      simp
    exact ⟨asum1, asum2⟩


  · -- prove lower bound.
    simp only [exists_prop, exists_and_left, Set.mem_setOf_eq,
    forall_exists_index, and_imp]
    rintro _ a apos asum rfl

    -- a0 / 1 = (a0+1) / 1 - 1, a1 / (1+a0) = (1+a0+a1)/(1+a0) - 1, ...
    have h1: ∀i∈ range n, a i / (1 + ∑j ∈ range i, a j) =
      (1 + ∑ j ∈ range (i+1), a j) / (1 + ∑j ∈ range i, a j) + -1 := by
      intro i ilt
      rw [Finset.sum_range_succ, ← add_assoc, add_div]
      have: 1 + ∑ j ∈ range i, a j ≠ 0 := by
        symm; apply ne_of_lt
        by_cases hi: i = 0
        · simp [hi]
        · have: 0 < ∑ j ∈ range i, a j := by
            apply sum_pos
            · intro j hj
              apply apos j
              simp only [mem_range] at ilt hj ⊢
              apply lt_trans hj ilt
            · simp [hi]
          linarith only [this]
      simp [this]

    -- so a0/1 + a1/(1+a0) + ... = (a0+1)/1 - 1 + (a0+a1+1)/(1+a0) - 1 + ...
    have h2: ∑ i ∈ range n, a i / (1 + ∑ j ∈ range i, a j) =
      ∑ i ∈ range n, (1 + ∑ j ∈ range (i+1), a j) / (1 + ∑ j ∈ range i, a j) - n := by
      rw [sum_congr rfl h1, sum_add_distrib]
      simp only [sum_neg_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
      rfl

    -- all a-term > 0, so sum of them ≥ 0 and 1 + sum > 0.
    have sumpos' {i:ℕ} (hi: i ≤ n):
      0 < 1 + ∑ j ∈ range i, a j := by
      have: 0 ≤ ∑ j ∈ range i, a j := by
        apply sum_nonneg (fun _ hj => ?_)
        apply le_of_lt (apos _ ?_)
        simp only [mem_range] at hj ⊢
        apply lt_of_lt_of_le hj hi
      linarith only [this]

    -- by AM-GM, x1+x2+...+xn ≥ n (x1x2...xn)^(1/n)
    -- notice that this AM-GM inequality take equal sign when x1=x2=...=xn.
    -- or, ai = 2^i. so when proving existence, we let ai = 2^i.
    have h3: ∑ i ∈ range n, (1 + ∑ j ∈ range (i+1), a j) / (1 + ∑ j ∈ range i, a j) ≥
      n * (∏ i ∈ range n, (1 + ∑ j ∈ range (i+1), a j) / (1 + ∑ j ∈ range i, a j))^(1/n:ℝ) := by
      set w : ℕ → ℝ := fun _ => 1/n with w_def
      have hw1: ∀ i ∈ range n, 0 ≤ w i := by
        simp [w_def]
      have hw2: ∑ i ∈ range n, w i = 1 := by
        simp only [w_def, one_div, sum_const, card_range, nsmul_eq_mul]
        simp [nposr.ne']
      set z: ℕ → ℝ := fun i =>
        (1 + ∑ j ∈ range (i+1), a j) / (1 + ∑ j ∈ range i, a j) with z_def
      have hz: ∀ i ∈ range n, 0 ≤ z i := by
        simp only [z_def]
        intro i hi
        apply div_nonneg
        all_goals
          apply le_of_lt (sumpos' ?_)
          simp only [mem_range] at hi
        · exact hi
        · apply le_of_lt hi
      have hh1 := Real.geom_mean_le_arith_mean_weighted (range n) w z hw1 hw2 hz
      simp only [w_def, ← mul_sum] at hh1
      have {A B : ℝ} (h: B ≤ 1/(n:ℝ) * A): A ≥ n*B := by
        have: A = n * (1/(n:ℝ) * A) := by
          simp [nposr.ne']
        rw [this]
        apply (mul_le_mul_iff_of_pos_left nposr).mpr h
      rw [Real.finset_prod_rpow _ _ hz _] at hh1
      apply this hh1

    -- compute those product, which is 1+a0+a1+...+a_{n-1}
    have h4 {m:ℕ} (hm1: m ≥ 1)(hm2: m ≤ n):
      ∏ i ∈ range m, (1 + ∑ j ∈ range (i+1), a j) / (1 + ∑ j ∈ range i, a j) =
        1 + ∑ i ∈ range m, a i := by
      induction' m,hm1 using Nat.le_induction with m hm1 ih
      · simp
      · have hm3: m ≤ n := by linarith only [hm2]
        rw [prod_range_succ, ih hm3]
        refine mul_div_cancel₀ _ ?_
        exact (sumpos' hm3).ne'

    -- by problem statement, 1+a0+a1+...+a_{n-1} = 2^n-1, substitute back.
    rw [h4 nge1 le_rfl, asum, add_sub_cancel, ← Real.rpow_natCast_mul (by norm_num)] at h3
    simp only [one_div, ne_eq, nposr.ne', not_false_eq_true, mul_inv_cancel₀,
    Real.rpow_one] at h3
    rw [h2]
    linarith only [h3]