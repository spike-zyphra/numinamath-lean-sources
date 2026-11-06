import Mathlib

open Finset

/- 14. $[8]$ Evaluate the infinite sum $\sum_{n=1}^{\infty} \frac{n}{n^{4}+4}$. -/
theorem algebra_153570 : ∑' n : ℕ, (n / (n ^ 4 + 4 : ℝ)) = 3 / 8 := by
  -- Rewrite the theorem statement in terms of HasSum
  suffices HasSum (fun n : ℕ => n / (n ^ 4 + 4 : ℝ)) (3 / 8) from this.tsum_eq
  -- Rewrite the theorem statement as
  -- Filter.Tendsto (fun n ↦ ∑ i ∈ range n, i / (i ^ 4 + 4 : ℝ)) Filter.atTop (nhds (3 / 8))
  rw [hasSum_iff_tendsto_nat_of_nonneg (by intro _; positivity)]
  -- Show that the finite sum ∑ i ∈ range k, i / (i ^ 4 + 4 : ℝ) = 3 / 8 - 1 / 4 * (1 / (k ^ 2 + 1 : ℝ) + 1 / ((k - 1) ^ 2 + 1 : ℝ))
  -- for all k > 2
  have sum_eq k (hk : k > 2) : ∑ n ∈ range k, n / (n ^ 4 + 4 : ℝ) = 3 / 8 - 1 / 4 * (1 / (k ^ 2 + 1 : ℝ) + 1 / ((k - 1) ^ 2 + 1 : ℝ)) := calc
    ∑ n ∈ range k, n / (n ^ 4 + 4 : ℝ) = ∑ n ∈ Ico 1 k, n / (n ^ 4 + 4 : ℝ) := by
        rw [sum_range_eq_add_Ico _ (by omega)]
        norm_num
    -- observe that n / (n ^ 4 + 4) = 1 / ((n - 1) ^ 2 + 1) - (1 / (n + 1) ^ 2 + 1)
    _ = 1 / 4 * ∑ n ∈ range (k - 1), (1 / (n ^ 2 + 1 : ℝ) - 1 / ((n + 2) ^ 2 + 1)) := by
        rw [sum_Ico_eq_sum_range, mul_sum]
        apply sum_congr rfl
        intro n _
        push_cast
        field_simp
        ring
    _ = 1 / 4 * (3 / 2 + ∑ n ∈ Ico 2 (k - 1), (1 / (n ^ 2 + 1 : ℝ)) - ∑ n ∈ Ico 2 (k + 1), 1 / (n ^ 2 + 1 : ℝ)) := by
        rw [sum_sub_distrib]
        rw [sum_range_eq_add_Ico _ (by omega), sum_eq_sum_Ico_succ_bot (by omega)]
        nth_rw 3 [sum_Ico_eq_sum_range]
        norm_num [show k + 1 - 2 = k - 1 by omega, ←add_assoc, add_comm]
    -- many terms of the sum cancel each other and we get the final result
    _ = 3 / 8 - 1 / 4 * (1 / (k ^ 2 + 1 : ℝ) + 1 / ((k - 1) ^ 2 + 1 : ℝ)) := by
        rw [show k + 1 = ((k - 1) + 1) + 1 by omega]
        rw [sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega)]
        rw [show k - 1 + 1 = k by omega]
        push_cast [show k ≥ 1 by omega]
        ring
  -- we have that the sum is eventually equal to 3 / 8 - 1 / 4 * (1 / (k ^ 2 + 1 : ℝ) + 1 / ((k - 1) ^ 2 + 1 : ℝ))
  have sum_eq' : (fun k : ℕ => 3 / 8 - 1 / 4 * (1 / (k ^ 2 + 1 : ℝ) + 1 / ((k - 1) ^ 2 + 1 : ℝ))) =ᶠ[.atTop] (fun k : ℕ => ∑ n ∈ range k, n / (n ^ 4 + 4 : ℝ)) := by
    simp_rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 3
    intro k hk
    rw [sum_eq k (by omega)]
  -- find the limit of 3 / 8 - 1 / 4 * (1 / (k ^ 2 + 1 : ℝ) + 1 / ((k - 1) ^ 2 + 1 : ℝ))
  apply Filter.Tendsto.congr' sum_eq'
  clear * -
  nth_rw 2 [show (3 / 8 : ℝ) = 3 / 8 - 1 / 4 * (0 + 0) by norm_num]
  apply Filter.Tendsto.const_sub
  apply Filter.Tendsto.const_mul
  -- show that the limit of 1 / ((k + a)^2 + 1) is 0 for any real constant a
  have h (a : ℝ) : Filter.Tendsto (fun k : ℕ => 1 / ((k + a) ^ 2 + 1 : ℝ)) .atTop (nhds 0) := by
    simp only [NormedAddCommGroup.tendsto_atTop, sub_zero, norm_inv, Real.norm_eq_abs]
    intro e he
    -- find k such that |1 / ((k + a)^2 + 1)| < e for all n ≥ k
    have ⟨k, hk⟩ := exists_nat_gt (1 / e + 1 - a)
    use k
    intro n hn
    rw [abs_of_pos (by positivity), one_div_lt (by positivity) he]
    replace hn : 1 / e + 1 < n + a := by rify at hn; linarith
    have ineq : 0 ≤ n + a := by
      apply le_trans _ (le_of_lt hn)
      positivity
    rw [←sq_lt_sq₀ (by positivity) ineq] at hn
    trans (1 / e + 1) ^ 2 <;> nlinarith
  -- the result follows from lim (1 / (k ^ 2 + 1)) = 0 and lim (1 / (k - 1) ^ 2 + 1) = 0
  apply Filter.Tendsto.add
  · convert h 0
    simp only [add_zero]
  · exact h (-1)