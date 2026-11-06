import Mathlib

open Finset

/- Find a formula for the product of powers of 2 from \( j = 1 \) to \( n \), specifically \( \prod_{j=1}^{n} 2^{j} \). -/
theorem number_theory_4475 (n : ℕ) :
    ∏ j ∈ Icc 1 n, 2^j = 2^(n * (n + 1) / 2) := by
  -- Transform production into summation.
  rw [prod_pow_eq_pow_sum]
  congr
  -- Show 1+2+...+n = n(n+1)/2 .
  calc
    _ = ∑ i ∈ Ioc 0 n, i := by congr
    _ = (∑ i ∈ Icc 0 n, i) - 0 := by
      apply Nat.eq_sub_of_add_eq'
      apply Finset.add_sum_Ioc_eq_sum_Icc (f := id)
      simp
    _ = _ := by
      nth_rw 1 [show n = n + 1 - 1 by simp]
      rw [← Nat.range_eq_Icc_zero_sub_one _ (by simp), Finset.sum_range_id]
      simp only [add_tsub_cancel_right, tsub_zero]
      rw [mul_comm]
