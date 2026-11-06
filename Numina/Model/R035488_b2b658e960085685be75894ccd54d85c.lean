import Mathlib

open Finset

theorem algebra_300092 {f : ℤ → ℤ} (hf : ∀ x, f x = 3 * x + 2) :
    ∃ m, 1988 ∣ f^[100] m := by
  use 1520
  norm_num [Function.iterate_succ_apply, hf]