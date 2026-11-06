import Mathlib

open Real

/- Find

$$
\{\ln (1+e)\}+\left\{\ln \left(1+e^{2}\right)\right\}+\left\{\ln \left(1+e^{4}\right)\right\}+\left\{\ln \left(1+e^{8}\right)\right\}+\cdots,
$$

where $\{x\}=x-\lfloor x\rfloor$ denotes the fractional part of $x$. -/
theorem algebra_611373:
  ∑' (i:ℕ), (Int.fract (log (1 + exp (2^i)))) = 1 - log ((exp 1) - 1) := by

  -- easy to notice that ln (1 + e^(2^i)) > ln (e^(2^i))
  -- fractional part is ln (1 + e^(2^i)) - ln (e^(2^i)) = ln (1 + e^(- 2^i))
  have h_fract (i:ℕ): Int.fract (log (1 + exp (2^i))) =
    log (1 + exp (- 2^i)) := by
    have h1:log (1 + exp (2^i)) > log (exp (2^i)) := by
      rw [gt_iff_lt, log_lt_log_iff (exp_pos _)
        (by simp [add_pos, exp_pos (2^i)])]
      simp
    have h2: log (1 + exp (2^i)) < log (exp (2^i + 1)) := by
      rw [log_lt_log_iff (by simp [add_pos, exp_pos (2^i)]) (exp_pos _)]
      rw [exp_add]
      have hh1: 1 + exp (2^i) < exp (2^i) * 2 := by
        rw [mul_two]
        simp only [add_lt_add_iff_right, one_lt_exp_iff,
        Nat.ofNat_pos, pow_pos]
      have hh2: exp (2^i) * 2 < exp (2^i) * exp 1 := by
        rw [mul_lt_mul_left (exp_pos _)]
        linarith only [Real.exp_one_gt_d9]
      apply hh1.trans hh2
    have h3: ⌊(log (1 + exp (2^i)))⌋ = 2^i := by
      rw [log_exp] at h1 h2
      rw [Int.floor_eq_iff]
      push_cast
      exact ⟨h1.le, h2⟩
    have: ↑((2:ℤ)^i) = log (exp (2^i)) := by
      simp only [Int.cast_pow, Int.cast_ofNat, log_exp]
    rw [← Int.self_sub_floor, h3, this]
    replace: 0 < 1 + exp (2^i) := by
      linarith only [exp_pos (2^i)]
    rw [← log_div this.ne' (exp_pos (2^i)).ne']
    congr 1
    field_simp [(exp_pos (2^i)).ne']
    rw [one_add_mul, ← exp_add]
    simp [add_comm]

  have h_fract': ∑' (i:ℕ), (Int.fract (log (1 + exp (2^i)))) =
    ∑' (i:ℕ), log (1 + exp (- 2^i)) := by
    congr 1
    funext i
    apply h_fract i

  -- write sum of log term into log of product term,
  have h1 (k:ℕ): ∑ i ∈ Finset.range k, log (1 + exp (- 2^i)) =
    log (∏ i ∈ Finset.range k, (1 + exp (- 2^i))) := by
    rw [log_prod]
    intro i hi
    symm; apply ne_of_lt
    simp [add_pos, exp_pos]

  -- each term ≥ 0
  have hnng (i:ℕ): 0 ≤ log (1 + exp (- 2^i)) := by
    rw [← h_fract i]
    simp only [Int.fract_nonneg]

  -- to calculate the product, notice that
  -- (1-q)(1+q)(1+q^2)...(1+q^(2^n)) = 1 - q^(2^(n+1))
  have aux {q:ℝ} (n:ℕ):
    (1-q) * (∏ i ∈ Finset.range n, (1 + q^(2^i))) =
      1 - q^(2^n) := by
    induction' n with n ih
    · simp
    · rw [Finset.prod_range_succ, ← mul_assoc, ih,
      mul_comm, ← sq_sub_sq]
      ring

  -- so the product term is  (1 - e^(-2^(k+1))) / (1 - e^(-1))
  have h2 (k:ℕ): ∏ i ∈ Finset.range k, (1 + exp (-2^i)) =
    ∏ i ∈ Finset.range k, (1 + (exp (-1))^(2^i)) := by
    apply Finset.prod_congr rfl (fun i _ => ?_)
    simp only [add_right_inj, exp_neg, inv_pow, exp_one_pow,
    Nat.cast_pow, Nat.cast_ofNat]

  set q: ℝ := exp (-1) with q_def
  have hq1: 0 < q := by
    simp [q_def, exp_pos]
  have hq2: q < 1 := by
    rw [q_def, exp_neg]
    apply inv_lt_one_of_one_lt₀
    linarith only [exp_one_gt_d9]

  replace h2 (k:ℕ): ∏ i ∈ Finset.range k, (1 + exp (-2^i)) =
    (1 - q^(2^k)) / (1-q) := by
    symm
    apply div_eq_of_eq_mul ?_ ?_
    · apply ne_of_gt
      linarith only [hq2]
    · rw [mul_comm, h2 k, aux k]

  replace h1: (fun n => ∑ i ∈ Finset.range n, log (1 + rexp (-2 ^ i))) =
    (fun n => log ((1 - q^(2^n)) / (1-q))) := by
    funext k
    rw [h1 k, h2 k]

  -- obviously 1 - q^(2^k) tends to 1 as k goes to infinity, since q < 1.
  have h3: Filter.Tendsto (fun (k:ℕ) => 1 - q^(2^k)) Filter.atTop (nhds 1) := by
    have: |q| < 1 := by
      rw [abs_lt]
      constructor <;> linarith only [hq1, hq2]
    replace := tendsto_pow_atTop_nhds_zero_of_abs_lt_one this
    replace: Filter.Tendsto (fun (k:ℕ) => q^(2^k)) Filter.atTop (nhds 0) := by
      rw [Metric.tendsto_atTop] at this ⊢
      intro ε hε
      rcases (this ε hε) with ⟨N, hN⟩
      use N
      intro n hn
      apply hN (2^n) ?_
      apply hn.trans ?_
      rify
      have: 1 + ↑(n:ℕ) * (1:ℝ) ≤ (1+1:ℝ)^n := by
        apply one_add_mul_le_pow (by norm_num)
      norm_num at this
      apply le_trans (by linarith only) this
    nth_rw 2 [← sub_zero 1]
    rwa [Filter.tendsto_const_sub_iff]

  -- then limit of the sum is 1 / (1-q)
  replace h3: Filter.Tendsto (fun (k:ℕ) => (1 - q^(2^k))/(1-q))
    Filter.atTop (nhds (1 / (1-q))) := by
    have: 0 < 1 - q := by linarith only [hq2]
    have hh1: (fun (k:ℕ) => (1 - q^(2^k))/(1-q)) =
      (fun (k:ℕ) => (1 - q^(2^k)) * (1 / (1-q))) := by
      funext k
      field_simp [this.ne']
    have hh2: (1 / (1-q)) = 1 * (1/(1-q)) := by
      field_simp [this.ne']
    rw [hh2, hh1]
    apply Filter.Tendsto.mul_const _ h3

  rw [h_fract']
  refine HasSum.tsum_eq ?_
  rw [hasSum_iff_tendsto_nat_of_nonneg hnng, h1]
  have: 1 - log ((exp 1) - 1) = log (1 / (1-q)) := by
    have: 1 / (1-q) = (exp 1) / (exp 1 - 1) := by
      have hh1: 0 < 1 - q := by linarith only [hq2]
      have hh2: exp 1 - 1 > 0 := by linarith only [exp_one_gt_d9]
      field_simp [hh1.ne', hh2.ne']
      rw [q_def]
      simp [mul_sub, ← exp_add]
    rw [this, log_div, log_exp]
    <;> apply ne_of_gt (by linarith only [exp_one_gt_d9])
  rw [this]
  apply Filter.Tendsto.log h3 ?_
  apply ne_of_gt (one_div_pos.mpr ?_)
  linarith only [hq2]