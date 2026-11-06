import Mathlib

open Real

theorem number_theory_302338 {k : ℕ} (hk : 0 < k) :
    ∃ m : ℕ, 0 < m ∧ ∃ n : ℤ, (fun r => r * ⌈r⌉)^[m] (k + 1 / 2) = n := by 
  use 1
  constructor
  · norm_num
  · refine ⟨(fun r => r * ⌈r⌉) (k + 1 / 2), by simp⟩