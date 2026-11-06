import Mathlib

theorem algebra_229146 (a b c : ℤ) (ha : a ≠ 0) (h : a * x + b = c) (h1 : a = b + c) :
    ∃ n : ℤ, x = n := by
  exact ⟨x, by rfl⟩