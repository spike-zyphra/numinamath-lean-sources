import Mathlib

theorem number_theory_152 (n : ℕ) (h₀ : ∃ k, n = k^2) (h₁ : n ∈ Finset.Icc 10000 99999)
    (h₂ : n % 100 = 10 * (n / 100) + (n % 100) % 10) :
    n % 100 = 88 := by 
  rw [Finset.mem_Icc] at h₁
  rcases h₀ with ⟨k, rfl⟩
  rcases h₁ with ⟨h₃, h₄⟩
  have h5 : k ≥ 100 := by nlinarith
  have h6 : k ≤ 316 := by nlinarith
  interval_cases k <;> norm_num at *
  <;> omega