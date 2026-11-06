import Mathlib

/-Determine the exact value of the series
\[\frac{1}{5 + 1} + \frac{2}{5^2 + 1} + \frac{4}{5^4 + 1} + \frac{8}{5^8 + 1} + \frac{16}{5^{16} + 1} + \dotsb.\]-/
theorem algebra_11551 : ∑' n : ℕ, (2 ^ n : ℝ) / (5 ^ (2 ^ n) + 1) = 1 / 4 := by
-- Rewrite the goal in terms of partial sums in $ε$-$δ$ language
  apply HasSum.tsum_eq; rw [hasSum_iff_tendsto_nat_of_nonneg, Metric.tendsto_atTop]
  simp only [dist]; intro ε hε
  use (⌊Real.logb ((2:ℝ)/5) ε⌋.natAbs+1); intro n hn; rw [ge_iff_le] at hn
-- For later use, prove the following lemma by induction
  have lm1 : ∀ n : ℕ, (5 : ℝ) ^ n < 5 ^ 2 ^ n - 1 := by
    intro n; induction n with
    | zero => norm_num
    | succ n ih =>
      by_cases h' : n < 1; simp at h'; rw [h']; norm_num
      push_neg at h'
      have : (5 : ℝ) ^ (n + 1) ≤ 5 ^ (2 * n) := by
        rw [show (5:ℝ)=(5:ℕ) by rfl]; norm_cast
        rw [Nat.pow_le_pow_iff_right]; linarith; norm_num
      have : (5 : ℝ) ^ (2 * n) < (5 ^ 2 ^ n - 1) * (5 ^ 2 ^ n - 1) := by
        rw [two_mul, pow_add]; apply mul_lt_mul; assumption; linarith
        apply pow_pos; norm_num; simp; rw [one_le_pow_iff_of_nonneg]
        norm_num; norm_num; rw [Nat.ne_zero_iff_zero_lt]
        apply Nat.pow_pos; norm_num
      have : (5 ^ 2 ^ n - 1) * (5 ^ 2 ^ n - 1) < (5 ^ 2 ^ n - 1) * ((5:ℝ) ^ 2 ^ n + 1) := by
        rw [mul_lt_mul_left]; linarith; simp
        apply one_lt_pow; norm_num
        rw [Nat.ne_zero_iff_zero_lt]
        apply Nat.pow_pos; norm_num
      rw [show (5:ℝ)^2^(n+1)-1 = (5^2^n-1)*(5^2^n+1) by ring]; linarith
-- Prove the following lemma which will be used later to rewrite our series as a telescoping series
  have lm2 : ∀ n : ℕ, (2 ^ n : ℝ) / (5 ^ (2 ^ n) + 1) =
  2 ^ n / (5 ^ (2 ^ n) - 1) - 2 ^ (n + 1) / (5 ^ (2 ^ (n + 1)) - 1) := by
    intro m; rw [show (5:ℝ)^2^(m+1)-1 = (5^2^m-1)*(5^2^m+1) by ring]
    have : 0 < (5:ℝ) ^ 2 ^ m - 1 := by
      simp; apply one_lt_pow; norm_num
      rw [Nat.ne_zero_iff_zero_lt]; apply Nat.pow_pos; norm_num
    have : 0 < (5:ℝ) ^ 2 ^ m + 1 := by
      have : 0 ≤ (5:ℝ) ^ 2 ^ m := by apply pow_nonneg; norm_num
      linarith
    have aux: ((5:ℝ) ^ 2 ^ m - 1) * (5 ^ 2 ^ m + 1) ≠ 0 := by
      apply mul_ne_zero; linarith; linarith
    rw [← mul_right_inj' aux, mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀]
    rw [mul_sub]
    nth_rw 2 [mul_comm]; rw [← mul_assoc, div_mul_cancel₀]
    rw [← mul_div_assoc, mul_div_cancel_left₀]; ring
    assumption; linarith; linarith
-- Apply the lemma Finset.eq_sum_range_sub to the series $2^n/(5^(2^n)-1)$
  have tele := Finset.eq_sum_range_sub (fun n => (2 ^ n : ℝ) / (5 ^ (2 ^ n) - 1)) n
-- Rewrite tele and simplify the final goal
  norm_num1 at tele; apply_fun (fun x => (1:ℝ)/4 - x) at tele
  rw [sub_add_cancel_left, ← Finset.sum_neg_distrib] at tele
  simp only [neg_sub, ← lm2] at tele
  rw [← tele]; norm_num; rw [abs_eq_self.mpr]
-- Apply lemma lm1 to show that the LHS is less than $(2/5)^n$
  have : (2 ^ n : ℝ) / (5 ^ 2 ^ n - 1) < (2 / 5) ^ n := by
    rw [div_pow, div_lt_div_left]; apply lm1
    apply pow_pos; norm_num; simp
    apply one_lt_pow; norm_num
    rw [Nat.ne_zero_iff_zero_lt]; apply Nat.pow_pos; norm_num
    apply pow_pos; norm_num
-- By our specific choice of $n$, $(2/5)^n$ has to be less than $ε$
  have : ((2 : ℝ) / 5) ^ n < ε := by
    have : ((2 : ℝ) / 5) ^ n ≤ (2 / 5) ^ (⌊Real.logb ((2:ℝ)/5) ε⌋.natAbs + 1) := by
      apply pow_le_pow_of_le_one; norm_num; norm_num; assumption
    have : (2 / 5) ^ (⌊Real.logb ((2:ℝ)/5) ε⌋.natAbs + 1) < ε := by
      have : ((2:ℝ) / 5) ^ (⌊Real.logb ((2:ℝ)/5) ε⌋.natAbs + 1) < (2 / 5) ^ (Real.logb ((2:ℝ)/5) ε) := by
        rw [← Real.rpow_natCast]; rw [Real.rpow_lt_rpow_left_iff_of_base_lt_one]
        norm_num;
        have aux1:= Int.lt_floor_add_one (Real.logb (2 / 5) ε)
        have := @Int.le_natAbs ⌊Real.logb (2 / 5) ε⌋
        rify at this
        have : |(⌊Real.logb (2 / 5) ε⌋:ℝ)| = ⌊Real.logb (2 / 5) ε⌋.natAbs := by
          norm_cast; rw [show (⌊Real.logb (2 / 5) ε⌋.natAbs:ℝ)=(⌊Real.logb (2 / 5) ε⌋.natAbs:ℤ) by rfl]
          norm_cast
        linarith; any_goals norm_num
      rw [Real.rpow_logb] at this; linarith
      any_goals norm_num; assumption
      any_goals norm_num
    linarith
-- Use "linarith" to finish the goal and the rest goals are trivial
  linarith; apply div_nonneg; apply pow_nonneg; norm_num
  simp; rw [one_le_pow_iff_of_nonneg]; any_goals norm_num
  intro i; apply div_nonneg; apply pow_nonneg; norm_num
  have : 0 < (5:ℝ) ^ 2 ^ i := by apply pow_pos; norm_num
  linarith