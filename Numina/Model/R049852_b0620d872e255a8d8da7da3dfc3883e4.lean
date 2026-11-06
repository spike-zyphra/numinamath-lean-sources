import Mathlib

theorem number_theory_295761 (n : ℕ) (h : n = 2) :
    ∃ k, n * 8 ^ k = 64 ∨ n * 2 ^ (2011 - k) = 2 ^ 2011 := by
  rw [h]
  use 1
  simp
  <;> omega