import Mathlib

theorem number_theory_283838 (n : ℕ) (hn : n ≠ 0) (h : ∃ k : ℤ, (2^n - 2)/n = k) :
    ∃ m : ℤ, ((2^(2^n - 1) - 2)/(2^n - 1)) = m := by
  refine' ⟨(2 ^ (2 ^ n - 1) - 2) / (2 ^ n - 1), rfl⟩