import Mathlib

open Finset

theorem algebra_221957 {f : ℕ → ℕ} (hf : f = fun x => 3 * x + 2) :
    ∃ m, 0 < m ∧ 1988 ∣ f^[100] m := by
  use 1520
  constructor
  · norm_num
  · rw [hf]
    native_decide