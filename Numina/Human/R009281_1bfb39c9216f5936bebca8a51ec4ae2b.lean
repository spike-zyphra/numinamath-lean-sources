import Mathlib

open Finset Real

/- To be proven, that for every integer $n$ greater than 1,


$$

\frac{1}{n}+\frac{1}{n+1}+\frac{1}{n+2}+\ldots+\frac{1}{n^{2}-1}+\frac{1}{n^{2}}>1

$$
 -/
theorem inequalities_239823 (n : ℕ) (hn : 1 < n) :
    ∑ i ∈ Finset.Icc n (n ^ 2), (1 : ℝ) / i > 1 := by
  -- Check that n + 1 < n ^ 2, this will be used later in multiple places
  have quadratic_inequality: ∀ n > 1, n + 1 < n ^ 2 := by
    intro n hn
    rw [gt_iff_lt, Nat.lt_iff_add_one_le] at hn
    norm_num at hn
    -- Use induction
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      rw [add_sq]
      simp
      calc
        k + 1 < k ^ 2 := ih
        _ < k ^ 2 + 2 * k := by linarith
  -- Rewrite the sum by splitting off the first and last term
  rw [gt_iff_lt, ← Ioc_insert_left (by nlinarith), ← Ioo_insert_right (by nlinarith), sum_insert (by simp; nlinarith), sum_insert (by simp)]
  -- Lower bound the remaining terms
  have lower_bound : ∀ x ∈ Ioo n (n ^ 2), 1 / n ^ 2 < 1 / (x : ℝ) := by
    intro x hx
    -- Show x is positive
    have : 0 < (x : ℝ) := by
      rw [mem_Ioo] at hx
      trans (n : ℝ)
      · simp; linarith
      simp; exact hx.1
    rw [one_div_lt_one_div (by positivity) this]
    norm_cast
    rw [mem_Ioo] at hx
    tauto
  -- Use the bound on the sum
  have lb_sum : ∑ x ∈ Ioo n (n ^ 2), 1 / (n : ℝ) ^ 2 < ∑ x ∈ Ioo n (n ^ 2), 1 / (x : ℝ) := by
    apply sum_lt_sum
    · -- Use the lower bound
      intro i hi
      linarith [lower_bound i hi]
    -- Check conditions
    use n + 1
    constructor
    · rw [mem_Ioo]; simp; tauto
    -- Repeat the same logic
    refine lower_bound (n + 1) ?_
    rw [mem_Ioo]; simp; tauto
  -- Evaluate the lower bound sum
  have sum_eq : ∑ x ∈ Ioo n (n ^ 2), 1 / (n : ℝ) ^ 2 = (n ^ 2 - n - 1) / (n : ℝ) ^ 2 := by
    simp
    rw [div_eq_mul_inv]
    norm_cast; simp
    left
    -- Convert to integers
    norm_cast
    rw [Int.subNatNat_of_le (by nlinarith)]
    apply Int.natCast_sub
    have : _ := quadratic_inequality n hn
    rw [add_comm] at this
    refine le_of_lt (by linarith [Nat.lt_sub_of_add_lt this])
  -- Simplify lower bounded expression
  have expr_eq_one : 1 / n + (1 / n ^ 2 + (n ^ 2 - n - 1) / (n : ℝ) ^ 2) = 1:= by
    rw [div_add_div_same, ← mul_div_mul_right 1 (n : ℝ) (show (n : ℝ) ≠ 0 by positivity), ← pow_two, div_add_div_same]
    simp
    rw [div_self (by positivity)]
  rw [← gt_iff_lt]
  push_cast
  calc
    1 / (n : ℝ) + (1 / n ^ 2 + ∑ x ∈ Ioo n (n ^ 2), 1 / ↑x) > 1 / n + (1 / n ^ 2 + ∑ x ∈ Ioo n (n ^ 2), 1 / (n ^ 2 : ℝ)) := by linarith [lb_sum]
    _ = 1 / n + (1 / n ^ 2 + (n ^ 2 - n - 1) / (n : ℝ) ^ 2) := by linarith [sum_eq]
    _ = 1 := expr_eq_one