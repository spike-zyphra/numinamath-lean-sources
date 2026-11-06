import Mathlib

theorem number_theory_142355 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n % 15 = 0)
    (h₂ : (n / 100) % 10 = (n % 10)) :
    n = 525 ∨ n = 555 ∨ n = 585 := by
  rw [Finset.mem_Icc] at h₀ 
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> norm_num at h₁ h₂ <;> omega