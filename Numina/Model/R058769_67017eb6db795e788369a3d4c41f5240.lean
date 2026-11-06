import Mathlib

theorem number_theory_275520 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) :
    99 * n = 100 * (10 * (n / 10) + (n % 10) - 1) + (100 - (10 * (n / 10) + (n % 10))) := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁, h₂⟩
  interval_cases n <;> omega