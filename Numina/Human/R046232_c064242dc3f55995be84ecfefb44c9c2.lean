import Mathlib

def f (x : ℕ) := 3 * x + 2
/-let fx=3x+2.
 Prove that there exists a positive intege m such that
 f^(100)(m) is divisible by 2005-/
theorem number_theory_243316 :
    ∃ m, 0 < m ∧ 2005 ∣ f^[100] m := by
  use 380
  constructor
  · norm_num -- proves that 380 > 0
  · native_decide -- Lean can compute this divisibility directly