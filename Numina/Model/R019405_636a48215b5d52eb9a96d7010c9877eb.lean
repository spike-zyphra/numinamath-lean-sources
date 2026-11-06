import Mathlib

theorem number_theory_66211 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : ∃ k, n = k^2)
    (h₂ : ∃ a, (n / 100) % 100 = a * 11) (h₃ : ∃ b, (n % 100) % 100 = b * 11) :
    n = 7744 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  rcases h₁ with ⟨k, rfl⟩
  have h6 : k ≥ 32 := by
    nlinarith
  have h7 : k ≤ 99 := by
    nlinarith
  rcases h₂ with ⟨a, h₈⟩
  rcases h₃ with ⟨b, h₉⟩
  interval_cases k <;> norm_num at h₈ h₉ ⊢
    <;> omega