import Mathlib

theorem number_theory_184818 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : 11 ∣ n)
    (h₂ : n % 5 = 1) (h₃ : n % 7 = 3) :
    n = 451 ∨ n = 836 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h4, h5⟩
  interval_cases n <;> norm_num at h₁ h₂ h₃ ⊢ <;> omega