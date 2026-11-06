import Mathlib

open Finset

theorem number_theory_51598 (f : ℕ → ℕ) (hf : ∀ n, f n =  (Nat.digits 10 (n^10)).sum) : ∃ m, ∃ k, m ≠ k ∧ f^[m] 2000 = f^[k] 2000 := by
  use 4, 10 
  constructor
  · -- Show m ≠ k
    norm_num
  · -- Show f^[4] 2000 = f^[10] 2000
    simp_all [Function.iterate_succ_apply', hf]
    all_goals native_decide