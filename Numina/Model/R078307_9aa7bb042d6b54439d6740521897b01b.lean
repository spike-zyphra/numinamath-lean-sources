import Mathlib

theorem number_theory_108809 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : ∃ k, n = 100 * k + 10 * k + 5)
    (h₂ : n % m = 8) (h₃ : m ∈ Finset.Icc 1 9) :
    n = 665 ∧ m = 9 ∧ n / m = 73 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₁ with ⟨k, rfl⟩
  rw [Finset.mem_Icc] at h₃
  rcases h₀ with ⟨h₄, h₅⟩
  rcases h₃ with ⟨h₆, h₇⟩

  have h₈ : k < 10 := by
    omega
  interval_cases m <;> (interval_cases k <;> norm_num at h₂ ⊢ <;> try tauto)