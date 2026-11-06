import Mathlib

open Finset

theorem number_theory_78051 {a : ℕ → ℕ} (ha : ∀ n, a n < C * n)
    (ha' : StrictMono a) :
    {n | ∃ k, a n = 2005 * 10 ^ k}.Infinite := by 
  have h0 := ha 0
  simp at h0
  all_goals linarith