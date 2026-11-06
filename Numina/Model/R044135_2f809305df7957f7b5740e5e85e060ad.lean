import Mathlib

open Real

theorem number_theory_66195 (k : ℕ) : 
  ∃ m : ℕ, ∃ n : ℕ, 
    Nat.iterate (fun x : ℤ => Int.ceil ((x : ℝ) + (1/2 : ℝ))) m (k : ℤ) = n := by
  use 0
  use k
  simp
  <;> norm_num