import Mathlib

theorem number_theory_326686 (n m : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : m ∈ Finset.Icc 100 999)
    (h₂ : (n * 1000 + m) = 3 * (n * m)) : n * 1000 + m = 167334 := by
  rw [Finset.mem_Icc] at h₀ h₁
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h3 : n * 1000 + m = 3 * (n * m) := h₂
  interval_cases n <;> omega