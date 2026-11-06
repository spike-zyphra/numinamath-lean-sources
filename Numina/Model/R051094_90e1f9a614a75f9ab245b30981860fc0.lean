import Mathlib

theorem number_theory_194321 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n % 7 = 3) (h₂ : n % 9 = 5) (h₃ : n % 12 = 8) :
    n = 248 ∨ n = 500 ∨ n = 752 := by

  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩

  interval_cases n <;> norm_num at h₁ h₂ h₃ ⊢ <;> omega