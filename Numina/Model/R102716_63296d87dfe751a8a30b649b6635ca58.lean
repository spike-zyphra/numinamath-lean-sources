import Mathlib

theorem number_theory_233074 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    n = (Nat.digits 10 n).sum ^ 3 ↔ n = 512 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  constructor
  · -- Assume n equals the cube of the sum of its digits, prove n = 512
    intro h1
    interval_cases n <;> norm_num at h1 ⊢ <;> omega
  · -- Assume n = 512, prove it equals the cube of the sum of its digits
    intro h2
    rw [h2]
    norm_num