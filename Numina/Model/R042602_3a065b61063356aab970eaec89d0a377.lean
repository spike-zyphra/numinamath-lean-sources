import Mathlib

theorem number_theory_111868 (n : ℕ) : 2 ∣ n ↔ Even (n % 10) := by
  constructor
  · -- Assume 2 divides n, prove Even (n % 10)
    intro h
    have h1 : n % 2 = 0 := by
      omega
    have h2 : (n % 10) % 2 = 0 := by
      have h3 : (n % 10) % 2 = n % 2 := by
        omega
      omega
    exact ⟨n % 10 / 2, by omega⟩
  · -- Assume Even (n % 10), prove 2 divides n
    intro h
    have h1 : (n % 10) % 2 = 0 := by
      obtain ⟨k, hk⟩ := h
      omega
    have h2 : n % 2 = 0 := by
      have h3 : (n % 10) % 2 = n % 2 := by
        omega
      omega
    exact Nat.dvd_of_mod_eq_zero h2