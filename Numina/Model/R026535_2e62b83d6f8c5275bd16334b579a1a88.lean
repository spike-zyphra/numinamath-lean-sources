import Mathlib

open Finset

theorem algebra_151855 {f : ℕ → ℕ} (hf : f = fun x => 3 * x + 2) :
    ∃ m, 0 < m ∧ 1988 ∣ f^[100] m := by 
  use 1520
  constructor 
  · -- Show that 0 < 1520
    norm_num
  · -- Show that 1988 divides f^[100] 1520
    rw [hf]
    native_decide