import Mathlib

theorem number_theory_160201 : ¬ ∃ m, m^2 = 2^2017 := by
  intro h
  rcases h with ⟨m, hm⟩
  have h3 : m^2 = 2^2017 := hm
  have h4 : (m ^ 2).factorization 2 = 2017 := by
    rw [h3]
    native_decide
  have h5 : (m ^ 2).factorization 2 = 2 * (m.factorization 2) := by
    simp [Nat.factorization_pow]
  rw [h5] at h4
  have h6 : 2 * (m.factorization 2) = 2017 := h4
  have h7 : m.factorization 2 = 0 := by
    omega
  omega