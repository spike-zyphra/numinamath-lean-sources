import Mathlib

theorem number_theory_297081 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n % 10 ≠ 0)
    (h₂ : (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100)) - (n % 10) = n) :
    n = 495 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> norm_num at h₁ h₂ ⊢ <;> omega