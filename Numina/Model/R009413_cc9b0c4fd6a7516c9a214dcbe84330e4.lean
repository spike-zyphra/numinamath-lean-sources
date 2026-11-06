import Mathlib

open Finset

theorem algebra_98902 {u : ℕ → ℚ} (hu : ∀ r, u r = ∑ i in Icc 1 r, i) :
    ∑ i in Icc 1 100, (i / (∑ j in Icc 1 i, (1 / u j))) = 2575 := by
  norm_num [hu, sum_Icc_succ_top, div_eq_mul_inv]
  <;> native_decide