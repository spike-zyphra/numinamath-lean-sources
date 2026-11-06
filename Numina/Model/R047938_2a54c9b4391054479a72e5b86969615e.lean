import Mathlib

theorem number_theory_107362 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n % 10 ≠ 0)
    (h₂ : n = 56 * (n % 10)) :
    n / (n / 100 % 10) = 112 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> norm_num at h₂ h₁ ⊢ <;> all_goals omega