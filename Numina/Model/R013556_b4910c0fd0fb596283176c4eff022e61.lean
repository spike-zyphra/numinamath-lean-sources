import Mathlib

theorem number_theory_40485 (t : ℕ → ℕ)
    (ht : ∀ m, IsLeast {x | 0 < x ∧ ¬(m ∣ x)} (t m)) :
    ∀ n, ∃ m, m > n ∧ ¬∃ k, m = k + t k := by

  have h11 := ht 1 
  have h22 : t 1 ∈ {x | 0 < x ∧ ¬(1 ∣ x)} := h11.1

  have h55 : ¬ (1 ∣ t 1) := by 
    have h66 : t 1 ∈ {x | 0 < x ∧ ¬(1 ∣ x)} := h22
    have h44 : ¬ (1 ∣ t 1) := by 
      simpa using h66.2 
    tauto

  have h56 : (1 ∣ t 1) := by 
    simp [Nat.one_dvd] 

  exfalso 
  contradiction