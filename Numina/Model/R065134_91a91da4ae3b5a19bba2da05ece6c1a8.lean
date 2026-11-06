import Mathlib

theorem number_theory_148969 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    2 * n / 3 = Nat.factorial (n / 100) * Nat.factorial (n % 100 / 10) * Nat.factorial (n % 10) ↔ n = 432 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  constructor
  · -- Assume 2 * n / 3 = Nat.factorial (n / 100) * Nat.factorial (n % 100 / 10) * Nat.factorial (n % 10), prove n = 432
    intro h
    interval_cases n <;> norm_num [Nat.factorial] at h <;> omega
  · -- Assume n = 432, prove 2 * n / 3 = Nat.factorial (n / 100) * Nat.factorial (n % 100 / 10) * Nat.factorial (n % 10)
    intro h
    rw [h]
    norm_num [Nat.factorial]