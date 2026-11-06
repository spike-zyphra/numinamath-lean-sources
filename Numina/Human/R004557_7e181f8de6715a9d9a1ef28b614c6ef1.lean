import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- To be calculated $\lim _{n \rightarrow \infty}\left(\sqrt[3^{2}]{3} \cdot \sqrt[3^{3}]{3^{2}} \cdot \sqrt[3^{4}]{3^{3}} \ldots \sqrt[3^{n}]{3^{n-1}}\right)$. -/
theorem algebra_283669 :
    Tendsto (λ n => ∏ i ∈ range n, ((3 : ℝ) ^(i+1))^(1/(3^(i+2) : ℝ))) atTop (𝓝 (3^(1/4 : ℝ))) := by
  -- first convert the product to sum as all terms are power of fixed base
  have h_prod_to_sum (n : ℕ) : ∏ i ∈ range n, (3 ^ (i + 1)) ^ (1 / 3 ^ (i + 2) : ℝ) = (3 : ℝ) ^ (∑ i ∈ range n, ((i + 1 : ℝ) / 3 ^ (i + 2))) := by
    rw [Real.rpow_sum_of_pos (by norm_num)]
    congr
    ext i
    rw [show (3 : ℝ) ^ (i + 1) = (3 : ℝ) ^ (i + 1 : ℝ) by norm_cast]
    rw [← rpow_mul (by norm_num)]
    congr
    ring
  simp_rw [h_prod_to_sum]
  -- define the expression as power of two function, we'll prove the limit for both, since first function is 3, that is easy. we have to use two functions as mathlib doens't have const ^ f(x) yet
  let f (n : ℕ) := (3 : ℝ)
  let g (n : ℕ) := ∑ i ∈ range n, ((i + 1) / 3 ^ (i + 2) : ℝ)
  change Tendsto (fun n => (f n) ^ (g n)) atTop (𝓝 (3^(1/4)))
  refine Filter.Tendsto.rpow ?_ ?_ (by norm_num)
  . simp [f]
  . simp [g]
    -- to prove the sum's limit, first prove a formula for the expression
    have h_sum_formula (n : ℕ) (hn : 0 < n) : ∑ i ∈ range n, ((i + 1) / 3 ^ (i + 2 : ℝ) : ℝ) =
        1 / 6 * (∑ i ∈ range n, (1 / 3 : ℝ) ^ i) - 1 / 6 * n * (1 / 3) ^ n := by
      -- multiply sum by 1/3 note this almost shifts the sum upwards, not exact due to numerator
      have h_sum_one_div_three : (1 / 3) * ∑ i ∈ range n, ((i + 1) / 3 ^ (i + 2 : ℝ) : ℝ) =
          ∑ i ∈ range n, ((i + 1) / 3 ^ (i + 3 : ℝ) : ℝ) := by
        rw [Finset.mul_sum]
        congr
        ext i
        rw [mul_div, mul_comm, ← mul_div]
        congr
        rw [div_div, one_div]
        congr
        norm_cast
        ring
      calc
        -- subtract 1/3 * sum from sum to get 2 / 3 * sum = another expression
        _ = 3 / 2 * (∑ i ∈ range n, ((i + 1) / 3 ^ (i + 2 : ℝ) : ℝ) - ∑ i ∈ range n, ((i + 1) / 3 ^ (i + 3 : ℝ) : ℝ)) := by linarith
        -- convert rhs to Ico 0 n and Ico 1 (n + 1)
        _ = 3 / 2 * (∑ i ∈ Ico 0 n, ((i + 1) / 3 ^ (i + 2 : ℝ) : ℝ) - ∑ i ∈ Ico (0 + 1) (n + 1), (i / 3 ^ (i + 2 : ℝ): ℝ)) := by
          rw [range_eq_Ico]
          congr 2
          rw [← Finset.sum_Ico_add]
          congr
          ext i
          norm_cast
          ring_nf
        -- in rhs, break first Ico to 1 n and second Ico to 1 n
        _ = 3 / 2 * ((1 / (3 ^ 2) + ∑ i ∈ Ico 1 n, ((i + 1) / 3 ^ (i + 2 : ℝ) : ℝ)) - (∑ i ∈ Ico 1 n, (i / 3 ^ (i + 2 : ℝ): ℝ) + n / 3 ^ (n + 2))) := by
          congr
          . rw [Finset.sum_eq_sum_Ico_succ_bot hn]
            congr 1
            norm_num
          . rw [Finset.sum_Ico_succ_top (by linarith), show 0 + 1 = 1 by norm_num]
            congr 1
            norm_cast
        -- rearrange terms to subtract the sums in rhs
        _ = 3 / 2 * (1 / 3^2 + (∑ i ∈ Ico 1 n, ((i + 1) / 3 ^ (i + 2 : ℝ) : ℝ) - ∑ i ∈ Ico 1 n, (i / 3 ^ (i + 2 : ℝ): ℝ)) - n / 3 ^ (n + 2)) := by ring
        -- subtracting the sums, we get a more simpler term
        _ = 3 / 2 * (1 / 3^2 + ∑ i ∈ Ico 1 n, 1 / (3 : ℝ) ^ (i + 2) - n / 3 ^ (n + 2)) := by
          congr
          rw [← Finset.sum_sub_distrib]
          congr
          ext i
          norm_cast
          push_cast
          ring
        -- take in the first constant as 0th term
        _ = 3 / 2 * (∑ i ∈ Ico 0 n, 1 / (3 : ℝ) ^ (i + 2) - n / 3 ^ (n + 2)) := by
          rw [Finset.sum_eq_sum_Ico_succ_bot hn]
        -- multiply the 3
        _ = 1 / 2 * (∑ i ∈ Ico 0 n, 1 / (3 : ℝ) ^ (i + 1) - n / 3 ^ (n + 1)) := by
          rw [show (3 / 2 : ℝ) = 1/2 * 3 by ring, mul_assoc, mul_sub]
          congr 2
          . rw [Finset.mul_sum]
            congr; ext i
            ring
          . ring
        -- convert the expression to a sutiable format to use limit theorems later
        _ = 1 / 2 * (∑ i ∈ Ico 0 n, (1 / 3 : ℝ) ^ (i + 1) - n / 3 ^ (n + 1)) := by
          congr; ext i
          ring_nf

        _ = 1 / 2 * (∑ i ∈ range n, (1 / 3) ^ (i + 1) - (1/3) * ↑n * (1 / 3) ^ n) := by
          rw [range_eq_Ico]
          congr
          ring_nf
        _ = 1 / 6 * (∑ i ∈ range n, (1 / 3 : ℝ) ^ i) - 1 / 6 * n * (1 / 3) ^ n := by
          rw [mul_sub]
          congr 1
          . rw [show (1 / 6 : ℝ) = (1/2) * (1/3) by norm_num, mul_assoc, Finset.mul_sum (a := (1 / 3 : ℝ))]
            congr; ext i
            ring
          . ring
    -- the above formula works for 0 < n, i.e. eventually equal to our goal function so we can change the limit to use that
    convert_to Tendsto (fun n => 1 / 6 * (∑ i ∈ range n, (1 / 3 : ℝ) ^ i) - 1 / 6 * n * (1 / 3) ^ n) atTop (𝓝 4⁻¹) using 0
    . apply Filter.tendsto_congr'
      simp [EventuallyEq]
      use 1
      rintro i hi
      simp at h_sum_formula
      specialize h_sum_formula i hi
      convert h_sum_formula
      norm_cast
    -- now use subtraction of limit
    rw [show (4 : ℝ)⁻¹ = 4⁻¹ - 0 by norm_num]
    apply Filter.Tendsto.sub
    -- first limit is basically geometric series
    . rw [show (4 : ℝ)⁻¹ = 1 / 6 * (3 / 2) by norm_num]
      apply Filter.Tendsto.const_mul
      convert HasSum.Multipliable.tendsto_sum_tsum_nat (summable_geometric_of_lt_one (show 0 ≤ (1 / 3 : ℝ) by norm_num) (by norm_num))
      rw [eq_comm, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    -- second limit boils down to n * r ^ n tends to 0 for infinity when 0 <= r < 1
    . simp_rw [mul_assoc]
      rw [show (0 : ℝ) = 1/6 * 0 by norm_num]
      apply Filter.Tendsto.const_mul
      apply tendsto_self_mul_const_pow_of_abs_lt_one
      rw [abs_eq_self.mpr] <;> norm_num