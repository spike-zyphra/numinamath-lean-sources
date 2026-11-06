import Mathlib

open Finset

theorem algebra_181999 {f : ℕ → ℕ} (hf : ∀ x, f x = 3 * x + 2) :
    ∃ m, 0 < m ∧ 1988 ∣ f^[100] m := by 
  use 1520 
  constructor 
  · -- Show m is positive.
    norm_num 
  · -- Show 1988 divides f^[100] 1520 
    simp_all [Function.iterate_succ_apply', hf]
    <;> native_decide