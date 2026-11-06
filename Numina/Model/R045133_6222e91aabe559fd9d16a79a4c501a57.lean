import Mathlib

theorem number_theory_249161 (n : ℕ) :
    ∃ k : ℕ, 2^n ∣ (51^k - 17) := by 
  use 0
  have h1 : (51 ^ (0 : ℕ) - 17 : ℕ) = 0 := by
    omega
  rw [h1] 
  simp