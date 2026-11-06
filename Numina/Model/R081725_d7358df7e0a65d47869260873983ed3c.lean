import Mathlib

theorem number_theory_191514 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : 7 ∣ n - 6)
    (h₂ : 8 ∣ n - 7) (h₃ : 9 ∣ n - 8) : n = 503 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> omega