import Mathlib

/-- The difference between 1/3 and the decimal 0.33…3 (k copies of 3) equals 1 / (3 * 10^k). -/
theorem one_third_sub_k (k : ℕ) (hk : k > 0) :
  (1 : ℚ) / 3 - (∑ i in Finset.range k, (3 : ℚ) / 10 ^ (i + 1))
    = 1 / (3 * 10 ^ k : ℚ) := by

  have A : ∑ i in Finset.range k, (3 : ℚ) / 10 ^ (i + 1) = (1 - 1 / 10 ^ k) / 3 := by
    -- Expand the finite geometric series
    calc
      ∑ i in Finset.range k, ((3 : ℚ) / 10 ^ (i + 1))
      _ = ∑ i in Finset.range k, (3 : ℚ) / 10 * (1 / 10 ^ i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring

      -- factor out 3/10
      _ = (3 : ℚ) / 10 * ∑ i in Finset.range k, (1 / 10 ^ i) := by
          exact Eq.symm (Finset.mul_sum (Finset.range k) (fun i ↦ 1 / 10 ^ i) (3 / 10))

      -- change 1/10^i to (1/10)^i
      _ = (3 : ℚ) / 10 * ∑ i in Finset.range k, (1 / 10) ^ i := by
          apply congrArg (fun x => (3 : ℚ) / 10 * x)
          apply Finset.sum_congr rfl
          intro i _
          exact Eq.symm (one_div_pow 10 i)

      -- sum of geometric series
      _ = (3 / 10) * (((1 / 10) ^ k - 1) / (1 / 10 - 1)) := by
        -- geom_sum for a = 1/10 ≠ 1
        have h : (1 / 10 : ℚ) ≠ 1 := by norm_num
        have h1:k>0:=by exact hk
        rw [geom_sum_eq h]

      -- simplify
      _ = (1 - 1 / 10 ^ k) / 3 := by
        field_simp
        ring

  -- Subtract from 1/3
  calc
    (1 : ℚ) / 3 - ∑ i in Finset.range k, (3 : ℚ) / 10 ^ (i + 1)
      = (1 : ℚ) / 3 - (1 - 1 / 10 ^ k) / 3 := by rw [A]
    _ = 1 / 10 ^ k / 3 := by 
      field_simp
    _ = 1 / (3 * 10 ^ k : ℚ) := by 
      field_simp
      ring
