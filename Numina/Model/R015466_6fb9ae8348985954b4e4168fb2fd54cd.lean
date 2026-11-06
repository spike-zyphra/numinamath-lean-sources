import Mathlib

open Finset

theorem algebra_318514 {f : ℕ → ℕ} (hf : ∀ x, f x = 3 * x + 2) :
    ∃ m, 0 < m ∧ 1988 ∣ f^[100] m := by 
  use 1520
  constructor
  · norm_num
  · -- Show that 1988 divides f^[100] 1520
    norm_num [Function.iterate_succ_apply', hf]