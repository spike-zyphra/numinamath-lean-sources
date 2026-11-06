import Mathlib

theorem number_theory_168761 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : 2 ∣ n) (h₂ : 3 ∣ n)
    (h₃ : 4 ∣ n) (h₄ : 6 ∣ n) (h₅ : 7 ∣ n) (h₆ : 8 ∣ n) (h₇ : 9 ∣ n) (h₈ : 12 ∣ n)
    (h₉ : 14 ∣ n) :
    n = 504 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁₀, h₂₀⟩
  interval_cases n <;> omega