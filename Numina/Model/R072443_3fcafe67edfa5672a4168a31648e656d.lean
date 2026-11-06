import Mathlib

open Finset

theorem number_theory_240480 (f : ℕ → ℕ) (hf : f = fun x => 3 * x + 2) :
    ∃ m > 0, 1988 ∣ f^[100] m := by
  use 1520
  constructor
  · norm_num
  · rw [hf]
    native_decide