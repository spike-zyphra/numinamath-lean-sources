import Mathlib

/- Compute $\sum_{i=1}^{\infty} \frac{a i}{a^{i}}$ for $a>1$. -/
theorem algebra_610958 {a: ℝ} (ha: a > 1):
  ∑' (i:ℕ), (a*(i+1) / a^(i+1)) = (a / (1-a))^2 := by
  -- factor a out
  have h1: ∑' (i:ℕ), (a*(i+1) / a^(i+1)) =
    a * ∑' (i:ℕ), (i+1)/a^(i+1) := by
    rw [← tsum_mul_left]
    congr 1
    funext i
    ring
  have ha1: 0 ≤ 1/a := by positivity
  have ha2: 1/a < 1 := by
    refine (div_lt_one ?_).mpr ha
    positivity
  have ha3: 0 < a-1 := by linarith only [ha]
  have ha4 {n:ℕ}: a^n ≠ 0 := by
    have: 0 < a := by linarith only [ha]
    simp [this.ne']
  have ha5: 1-a < 0 := by linarith only [ha]

  -- recall some geometric sum equations.
  -- infinite sum of geometric sequence.
  have inf_geom_sum_1: ∑'(i:ℕ), 1 / a^i = a / (a-1) := by
    have: ∑' (i:ℕ), 1 / a^i = ∑' (i:ℕ), (1/a)^i := by
      congr 1; funext i
      rw [one_div_pow]
    rw [this, tsum_geometric_of_lt_one ha1 ha2]
    field_simp
  have inf_geom_sum_2: ∑' (j:ℕ), 1 / a^(j+1) = 1/(a-1) := by
    have: ∑' (j:ℕ), 1 / a^(j+1) = (1/a) * ∑' (j:ℕ), 1/a^j := by
      rw [← tsum_mul_left]
      congr 1; funext j
      rw [pow_succ]
      ring
    rw [this, inf_geom_sum_1]
    field_simp

  -- finite sum of geometric sequence.
  have fin_geom_sum {n:ℕ}: ∑ i ∈ Finset.range n, 1 / a^(i+1) =
    1/(a-1) - (1/a)^n/(a-1) := by
    have: ∑ i ∈ Finset.range n, 1 / a^(i+1) =
      (1/a) * ∑ i ∈ Finset.range n, (1/a)^i := by
      rw [Finset.mul_sum]
      congr 1; funext i
      ring
    rw [this, geom_sum_eq (by simp [ha.ne'])]
    field_simp [ha3.ne', ha4]
    have: a^n*(a-1) / (a^n*(1-a)) = -1 := by
      have: 1-a ≠ 0 := by
        apply ne_of_lt
        linarith only [ha3]
      field_simp [this]
      ring
    rw [mul_div_assoc, this]
    simp

  -- notice that 1/a+2/a^2+3/a^3+... = (1/a+1/a^2+..) + (1/a^2+1/a^3+...)
  have h2 {n:ℕ}: ∑i ∈ Finset.range n, ((i+1)/a^(i+1)) =
    ∑ i ∈ Finset.range n,
      (1/a^i) * (∑ j ∈ Finset.range (n-i), 1/a^(j+1)) := by
    induction' n with n ih
    · simp
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp only [add_tsub_cancel_left, Finset.range_one,
      Finset.sum_singleton, zero_add, pow_one]
      rw [add_div, ← add_assoc]
      congr 1
      · -- sum to (n+1-i) is sum to (n-i) add (n-i)-th term.
        have hh1: ∑i ∈ Finset.range n, (
          1/a^i * (∑ j ∈ Finset.range (n+1-i), (1/a^(j+1)))  ) =
          ∑ i ∈ Finset.range n, (
          1/a^i * (∑ j ∈ Finset.range (n-i), (1/a^(j+1)) + 1/a^(n-i+1))) := by
          apply Finset.sum_congr rfl ?_
          intro i hi
          congr 1
          have: ∑ j ∈ Finset.range (n+1-i), 1/a^(j+1) =
            ∑ j ∈ Finset.range (n-i+1), 1/a^(j+1) := by
            congr
            simp only [Finset.mem_range] at hi
            omega
          rw [this, Finset.sum_range_succ]
        have hh2: n / a^(n+1) = (Finset.range n).card • (1/a^(n+1)) := by
          simp only [Finset.card_range, nsmul_eq_mul]
          ring
        rw [hh1, hh2, Finset.sum_add_card_nsmul]
        apply Finset.sum_congr rfl ?_
        intro i hi
        rw [mul_add]; congr 1
        field_simp
        have: n+1 = i + (n-i+1) := by
          simp only [Finset.mem_range] at hi
          omega
        rw [this, pow_add _ i (n-i+1)]
      · ring

  -- and (1/a+1/a^2+...) + (1/a^2+1/a^3+...) + (...) is easy to calculate.
  -- that's exactly (1+1/a+1/a^2+...) multiple sum of infinite geometric sequence.
  -- the first factor is also sum of infinite geometric sequence.
  -- so result is a/(a-1) multiple (1/(a-1)) = a / (a-1)^2
  have h3: HasSum (fun i => (
      (1/a^i) * ∑' (j:ℕ), 1 / a^(j+1)
    )) (a/(a-1)  *  (1/(a-1))) := by
    rw [inf_geom_sum_2]
    apply HasSum.mul_right
    have h2: a/(a-1) = (1-(1/a))⁻¹ := by
      field_simp
    have h3: (fun i => 1/a^i) = (fun i => (1/a)^i) := by
      funext i; rw [one_div_pow]
    rw [h2, h3]
    apply hasSum_geometric_of_lt_one ha1 ha2

  -- we following intermediate result in later calculation.
  -- n r^n converges to zero if r < 1.
  have h4: Filter.Tendsto (fun (n:ℕ) => n*(1/a)^n/(a-1))
    Filter.atTop (nhds 0) := by
    have hh1 := tendsto_self_mul_const_pow_of_lt_one ha1 ha2
    have hh2: 1/(a-1) ≠ 0 := by
      symm; apply ne_of_lt
      apply div_pos (by norm_num)
      linarith only [ha]
    have hh2': a-1 ≠ 0 := by
      simp only [one_div, ne_eq, inv_eq_zero] at hh2
      simp [hh2]
    have hh3: (fun (n:ℕ) => n*(1/a)^n/(a-1)) =
      (fun (n:ℕ) => ((1/(a-1)) •( n*(1/a)^n))) := by
      funext n
      simp only [smul_eq_mul]
      field_simp
      simp [mul_comm]
    rw [← tendsto_const_smul_iff₀ hh2, smul_zero] at hh1
    rwa [hh3]

  -- combine above results, we claim infinite sum
  -- 1/a+2/a^2+3/a^3+... = (1/a+1/a^2+...) + (1/a^2+1/a^3+...) + ... = a / (a-1)^2.
  have h5: HasSum (fun (i:ℕ) => ((i+1)/a^(i+1)) ) (a/(a-1) * (1/(a-1))) := by
    have hh1: ∀(i:ℕ), 0 ≤ (fun (i:ℕ) => ((i+1)/a^(i+1))) i := by
      intro i; simp only
      apply div_nonneg
      all_goals positivity
    have hh2: ∀(i:ℕ), 0 ≤ (fun (i:ℕ) => (
        (1/a^i) * ∑' (j:ℕ), 1 / a^(j+1)
      )) i := by
      intro i; simp only
      apply mul_nonneg (by positivity) ?_
      rw [inf_geom_sum_2]
      apply div_nonneg (by norm_num) ?_
      linarith only [ha]
    -- we prove the goal by showing limit of the sum sequence is a/(a-1)^2.
    refine (hasSum_iff_tendsto_nat_of_nonneg hh1 _).mpr ?_
    rw [Metric.tendsto_atTop] at h4 ⊢
    rw [hasSum_iff_tendsto_nat_of_nonneg hh2, Metric.tendsto_atTop] at h3
    intro ε hε
    specialize h3 (ε/2) (by positivity)
    specialize h4 (ε/2) (by positivity)
    rcases h3 with ⟨N1, h3⟩
    rcases h4 with ⟨N2, h4⟩
    use max N1 N2
    intro n hn
    have hn1: n ≥ N1 := le_trans (Nat.le_max_left N1 N2) hn
    have hn2: n ≥ N2 := le_trans (Nat.le_max_right N1 N2) hn
    specialize h3 n hn1
    specialize h4 n hn2
    -- we separate the sum to two parts
    -- and claim limit of first part is a/(a-1)^2 as we already show.
    -- second part contain a term of the form n r^n with r < 1, and we already know its limit is 0.
    -- so whole limit is a/(a-1)^2.
    have hh3: ∑ i ∈ Finset.range n, (1 / a^i *
        ∑ j ∈ Finset.range (n-i), 1/a^(j+1) ) =
      ∑ i ∈ Finset.range n, (1/a^i * (1/(a-1)) - ((1/a)^n)/(a-1)) := by
      apply Finset.sum_congr rfl ?_
      intro i hi
      rw [fin_geom_sum, mul_sub]
      congr 1; rw [← mul_div_assoc]
      congr 1; rw [← one_div_pow, ← pow_add]
      congr 1; simp only [Finset.mem_range] at hi
      omega
    rw [h2, hh3, Finset.sum_sub_distrib,
    ← Finset.sum_div, Finset.sum_const]
    nth_rw 1 [← inf_geom_sum_2]
    simp only [Finset.card_range, nsmul_eq_mul]
    have real_dist_sub {A B C: ℝ} (hA: dist A C < ε/2)
      (hB: dist B 0 < ε/2): dist (A-B) C < ε := by
      rw [Real.dist_eq] at hA hB ⊢
      have: A - B - C = (A-C) - (B-0) := by ring
      rw [this]
      apply lt_of_le_of_lt (abs_sub _ _) ?_
      linarith only [hA, hB, hε]
    apply real_dist_sub h3 h4

  -- substitute the infinite sum value, done.
  rw [h1, HasSum.tsum_eq h5]
  field_simp
  have h6: (a-1)*(a-1) = (1-a)^2 := by ring
  rw [h6, ← pow_two, mul_div_assoc]
  simp [ha5.ne]