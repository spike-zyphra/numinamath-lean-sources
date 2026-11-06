import Mathlib

theorem number_theory_247251 (a b : ℕ ) :
    5 * a ≥ 7 * b ↔ ∃ (x y z t : ℕ), a = x + 2*y + 3*z + 7*t ∧ b = y + 2*z + 5*t := by
  constructor
  · -- Assume 5a ≥ 7b.
    intro h
    have h2 : b ≤ 5 * a := by
      omega
    have h1 : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1)
    · -- case b % 5 = 0
      have h3 : b % 5 = 0 := h1
      have h4 : ∃ k : ℕ, b = 5 * k := by 
        refine' ⟨b / 5, by omega⟩ 
      rcases h4 with ⟨k, hk⟩
      use (a - 7 * k), 0, 0, k
      all_goals 
        omega
    · -- case b % 5 = 1
      have h3 : b % 5 = 1 := h1
      have h4 : ∃ k : ℕ, b = 5 * k + 1 := by 
        refine' ⟨b / 5, by omega⟩ 
      rcases h4 with ⟨k, hk⟩
      use (a - 2 - 7 * k), 1, 0, k
      all_goals 
        omega
    · -- case b % 5 = 2
      have h3 : b % 5 = 2 := h1
      have h4 : ∃ k : ℕ, b = 5 * k + 2 := by 
        refine' ⟨b / 5, by omega⟩ 
      rcases h4 with ⟨k, hk⟩
      use (a - 3 - 7 * k), 0, 1, k
      all_goals 
        omega
    · -- case b % 5 = 3
      have h3 : b % 5 = 3 := h1
      have h4 : ∃ k : ℕ, b = 5 * k + 3 := by 
        refine' ⟨b / 5, by omega⟩ 
      rcases h4 with ⟨k, hk⟩
      use (a - 5 - 7 * k), 1, 1, k
      all_goals 
        omega
    · -- case b % 5 = 4
      have h3 : b % 5 = 4 := h1
      have h4 : ∃ k : ℕ, b = 5 * k + 4 := by 
        refine' ⟨b / 5, by omega⟩ 
      rcases h4 with ⟨k, hk⟩
      use (a - 6 - 7 * k), 0, 2, k
      all_goals 
        omega
  · -- Assume there exists such x, y, z, t.
    rintro ⟨x, y, z, t, ha, hb⟩
    omega