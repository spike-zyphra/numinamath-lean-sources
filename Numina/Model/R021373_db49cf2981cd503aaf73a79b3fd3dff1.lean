import Mathlib

theorem algebra_242721 (n : ℕ) (h₀ : n ∈ Finset.Icc 1 100) :
    ∃ k, Real.logb 10 n = k + 5 / 10 ^ (Nat.digits 10 n).length := by 
  refine ⟨Real.logb 10 n - 5 / 10 ^ (Nat.digits 10 n).length, by simp⟩