import Mathlib

theorem number_theory_241062 :
    ∀ n : ℕ, ∃ k > n, Even k ∧ ∀ p : ℕ, Nat.Prime p → ¬Nat.Prime (p ^ 2 + k) := by
  intro n 
  use 66 * (n + 1) + 2
  constructor
  · -- Show $k > n$
    omega 
  constructor
  · -- Show $Even k$
    have h1 : Even (66 * (n + 1) + 2) := by
      have h2 : (66 * (n + 1) + 2) % 2 = 0 := by 
        omega
      exact ⟨(66 * (n + 1) + 2) / 2, by omega⟩
    exact h1
  · -- Show that for every prime $p$, $p^2 + k$ is composite
    intro p hp
    by_cases h : p ≤ 3
    · -- p ≤ 3
      have hp2 : p = 2 ∨ p = 3 := by 
        interval_cases p <;> norm_num at hp ⊢ <;> tauto
      rcases hp2 with (r | r)
      · -- p = 2
        rw [r]
        have h4 : ¬Nat.Prime (4 + (66 * (n + 1) + 2)) := by 
          have h2 : (4 + (66 * (n + 1) + 2)) % 2 = 0 := by
            omega 
          have h3 : 4 + (66 * (n + 1) + 2) > 2 := by 
            omega 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (4 + (66 * (n + 1) + 2)) by omega)
          all_goals omega 
        simpa using h4 
      · -- p = 3
        rw [r]
        have h5 : ¬Nat.Prime (9 + (66 * (n + 1) + 2)) := by
          have h4 : (9 + (66 * (n + 1) + 2)) % 11 = 0 := by 
            omega 
          have h5 : (9 + (66 * (n + 1) + 2)) > 11 := by 
            omega 
          apply Nat.not_prime_of_dvd_of_lt (show 11 ∣ (9 + (66 * (n + 1) + 2)) by omega)
          all_goals omega 
        simpa using h5 
    · -- p > 3
      have hp4 : p > 3 := by 
        omega 
      have hp1 : p % 3 = 1 ∨ p % 3 = 2 := by 
        by_contra h 
        push_neg at h 
        have h3p : p % 3 = 0 := by 
          omega 
        have h5p : ¬Nat.Prime p := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega 
        exfalso 
        exact h5p hp 
      have h3 : (p ^ 2 + (66 * (n + 1) + 2)) % 3 = 0 := by 
        rcases hp1 with (h | h)
        · -- Assume h : p % 3 = 1
          simp [Nat.add_mod, Nat.mul_mod, pow_two, h] 
        · -- Assume h : p % 3 = 2
          simp [Nat.add_mod, Nat.mul_mod, pow_two, h] 
      have h4 : ¬Nat.Prime (p ^ 2 + (66 * (n + 1) + 2)) := by
        have h5 : (p ^ 2 + (66 * (n + 1) + 2)) % 3 = 0 := h3
        have h6 : (p ^ 2 + (66 * (n + 1) + 2)) > 3 := by 
          nlinarith [show p ≥ 4 by omega, show 66 * (n + 1) + 2 ≥ 2 by omega] 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p ^ 2 + (66 * (n + 1) + 2)) by omega)
        all_goals omega 
      simpa using h4