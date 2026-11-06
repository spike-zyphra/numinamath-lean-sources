import Mathlib

open Nat

theorem number_theory_237263 {F : ℕ → ℕ} (hF : ∀ n, F n = F (n - 1) + F (n - 2)) (hF0 : F 0 = 0) (hF1 : F 1 = 1) (n : ℕ) :
    2 ^ (n - 1) * F n = ∑ k in Finset.Icc 0 ⌊(n - 1) / 2⌋₊, Nat.choose n (2 * k + 1) * 5 ^ k := by
  have h1 := hF 1
  simp at h1 hF1
  all_goals
    omega