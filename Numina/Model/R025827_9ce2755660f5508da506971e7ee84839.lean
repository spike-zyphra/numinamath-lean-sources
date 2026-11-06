import Mathlib

theorem number_theory_83604 (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (h1 : p 0 ≠ p 1) (h2 : p 0 ≠ p 2) (h3 : p 0 ≠ p 3)
    (h4 : p 1 ≠ p 2) (h5 : p 1 ≠ p 3) (h6 : p 2 ≠ p 3)
    (h7 : 2 * p 0 + 3 * p 1 + 5 * p 2 + 7 * p 3 = 162)
    (h8 : 11 * p 0 + 7 * p 1 + 5 * p 2 + 4 * p 3 = 162) :
    p 0 * p 1 * p 2 * p 3 = 570 := by
  have h9 : 9 * p 0 + 4 * p 1 = 3 * p 3 := by
    omega 
  have h14 : p 1 % 3 = 0 := by
    omega
  have hp1 : p 1 = 3 := by 
    have h13 : p 1 % 3 = 0 := h14
    have hp1 : Nat.Prime (p 1) := hp 1
    by_cases h10 : p 1 > 3
    · -- Assume p 1 > 3
      have h11 : ¬Nat.Prime (p 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p 1 by omega) (by omega) (by omega)
      contradiction
    · -- Assume p 1 ≤ 3
      have : p 1 ≤ 3 := by omega
      interval_cases p 1 <;> norm_num at hp1 h13 ⊢
  have hp3 : p 3 = 3 * p 0 + 4 := by 
    omega
  have h10 : 23 * p 0 + 5 * p 2 = 125 := by 
    omega
  have hp0 : p 0 = 5 := by
    have eq1 : 23 * p 0 + 5 * p 2 = 125 := h10
    have h17 : p 0 % 5 = 0 := by 
      omega
    have hp2 : Nat.Prime (p 0) := hp 0
    by_cases h18 : p 0 > 5
    · -- Assume p 0 > 5, this should be impossible
      have h19 : ¬Nat.Prime (p 0) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p 0 by omega) (by omega) (by omega)
      contradiction
    · -- Assume p 0 ≤ 5 
      have : p 0 ≤ 5 := by omega 
      have h11 : p 0 = 0 ∨ p 0 = 1 ∨ p 0 = 2 ∨ p 0 = 3 ∨ p 0 = 4 ∨ p 0 = 5 := by 
        omega
      rcases h11 with (r | r | r | r | r | r)
      · -- p 0 = 0 
        rw [show p 0 = (0 : ℕ) by omega] at hp2 
        norm_num at hp2 
      · -- p 0 = 1 
        rw [show p 0 = (1 : ℕ) by omega] at hp2 
        norm_num at hp2 
      · -- p 0 = 2 
        rw [show p 0 = (2 : ℕ) by omega] at h17 
        all_goals omega 
      · -- p 0 = 3 
        rw [show p 0 = (3 : ℕ) by omega] at h17 
        all_goals omega 
      · -- p 0 = 4 
        rw [show p 0 = (4 : ℕ) by omega] at hp2 
        norm_num at hp2 
      · -- p 0 = 5 
        omega 
  have hp2 : p 2 = 2 := by
    omega
  have hp3' : p 3 = 19 := by 
    omega
  calc 
    p 0 * p 1 * p 2 * p 3 = 5 * 3 * 2 * 19 := by 
      simp [hp0, hp1, hp2, hp3']
    _ = 570 := by norm_num