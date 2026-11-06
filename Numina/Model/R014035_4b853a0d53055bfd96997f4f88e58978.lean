import Mathlib

open Real
open scoped BigOperators

theorem number_theory_219591 {f : ℕ → ℕ} (hf : f = λ x => 3 * x + 2) :
  ∃ m, 0 < m ∧ 1988 ∣ f^[100] m := by 
  use 1520
  constructor
  · -- Show m is positive
    norm_num 
  · -- Unfold the function definition 
    rw [hf]
    native_decide