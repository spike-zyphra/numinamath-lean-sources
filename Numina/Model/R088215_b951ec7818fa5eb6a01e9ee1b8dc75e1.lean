import Mathlib

theorem number_theory_146050 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (100 * (n / 100 + 3) + 10 * ((n / 10) % 10 + 2) + (n % 10 + 1)) = 4 * n) :
    n = 107 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁₀, h₁₁⟩
  interval_cases n <;> norm_num at h₁ <;> omega