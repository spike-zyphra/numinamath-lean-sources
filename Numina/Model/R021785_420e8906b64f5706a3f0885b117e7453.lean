import Mathlib

theorem number_theory_230858 (n m : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : m ∈ Finset.Icc 100 999)
    (h₂ : (n * 1000 + m) = 3 * (n * m)) :
    n = 167 ∧ m = 334 := by
-- Expanding the range constraints for n and m
  rw [Finset.mem_Icc] at h₀ h₁
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
-- Use exhaustive search automatically in Lean, since n and m are bounded. Lean can check the value automatically.
  interval_cases n <;> omega