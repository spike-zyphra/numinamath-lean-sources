import Mathlib

theorem number_theory_274704 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : 100 * (n % 100) + 45 = n + 270) :
    100 * ((n / 100) % 100) + 198 = n := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h100, h999⟩
  interval_cases n <;> norm_num at h₁ ⊢ <;> omega