import Mathlib

theorem algebra_229943 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n / (n % 100) = 8 ∧ n % (n % 100) = 6) :
    n = 342 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  rcases h₁ with ⟨h₂, h₅⟩
  interval_cases n <;> norm_num at h₂ h₅ <;> omega