import Mathlib

theorem number_theory_161731 (n m : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : m ∈ Finset.Icc 100 999)
    (h₂ : 1000 * n + m = 7 * n * m) :
    n + m = 286 := by
  rw [Finset.mem_Icc] at h₀ h₁
  rcases h₀ with ⟨h₀1, h₀2⟩
  rcases h₁ with ⟨h₁1, h₁2⟩
  interval_cases n <;> omega