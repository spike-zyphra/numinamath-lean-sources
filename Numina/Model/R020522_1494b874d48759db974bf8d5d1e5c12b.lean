import Mathlib

theorem number_theory_294926 (n : ℕ) :
    (∃ k, n = k^2 + (k+1)^2) → ∃ m, m^2 = 2*n - 1 ∧
    (∃ m, m^2 = 2*n - 1) → ∃ k, n = k^2 + (k+1)^2 := by
  intro h
  rcases h with ⟨k, hk⟩
  use 2*k + 1
  intro h_1
  have h_eq1 : (2 * k + 1) ^ 2 = 2 * n - 1 := by 
    simpa using h_1.1
  have h_eq2 : ∃ m, m ^ 2 = 2 * n - 1 := h_1.2
  rcases h_eq2 with ⟨m_1, hm_1⟩
  exact ⟨k, hk⟩