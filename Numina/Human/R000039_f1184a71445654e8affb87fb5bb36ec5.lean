import Mathlib

open Finset Real Complex Polynomial

theorem precalculus_4077 {ω : ℂ} (hωval : ω = exp (2 * π * I / 11)) : ∏ i ∈ range 10, (2 - ω ^ (i + 1)) = 2047 := by
  have hω : IsPrimitiveRoot ω 11 := by
    convert isPrimitiveRoot_exp 11 (by simp)
  have H : X ^ 11 - 1 = ∏ i ∈ range 11, (X - C (ω ^ i)) := by
    simpa using X_pow_sub_C_eq_prod (α := 1) hω (by simp) (by norm_num)
  apply_fun (·.eval 2) at H
  rw [eval_prod, Finset.prod_range_succ'] at H
  norm_num at H
  exact H.symm
