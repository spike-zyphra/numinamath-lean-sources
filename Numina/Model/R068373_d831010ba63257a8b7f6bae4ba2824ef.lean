import Mathlib

theorem number_theory_110258 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    ¬∃ k, k = n / 10 ∧ k = n / 8 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀, h₁⟩
  rintro ⟨k, hk₁, hk₂⟩
  interval_cases n <;> omega