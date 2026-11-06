import Mathlib

theorem algebra_276186 {a : ℤ} (ha : a ≠ 0) (n : ℕ) (hn : n ≠ 1) :
    ∃ k : ℤ, ((a^(3*n)/(a^n-1) + 1/(a^n+1)) - (a^(2*n)/(a^n+1) + 1/(a^n-1))) = k := by 
  refine ⟨((a^(3*n)/(a^n-1) + 1/(a^n+1)) - (a^(2*n)/(a^n+1) + 1/(a^n-1))), rfl⟩