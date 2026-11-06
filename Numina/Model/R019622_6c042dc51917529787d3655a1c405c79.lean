import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem algebra_5904 {f : Polynomial ℤ} (hf : f.Monic)
  (d b c : ℤ) (hdb : d ∣ b - c) : d ∣ f.eval b - f.eval c := by
  have h1 : (b - c) ∣ (f.eval b - f.eval c) := by
    apply f.sub_dvd_eval_sub
  exact dvd_trans hdb h1