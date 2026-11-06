import Mathlib

theorem number_theory_312473 (a : ℕ) (ha : Nat.Prime a)
    (h7 : Nat.Prime (7 * a ^ 2 + 8)) (h8 : Nat.Prime (8 * a ^ 2 + 7)) :
    Nat.Prime (77 * a + 8) ∧ Nat.Prime (88 * a + 7) := by
  by_cases h : a > 3
  · -- Assume that a > 3
    have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
      omega
    rcases h1 with (h1 | h1 | h1)
    · -- a % 3 = 0
      have h1' : a % 3 = 0 := by tauto
      have h11 : a >= 4 := by
        omega
      have h2 : ¬Nat.Prime a := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ a by omega)
        all_goals omega
      contradiction
    · -- a % 3 = 1
      have h1' : a % 3 = 1 := by tauto
      have h11 : a ^ 2 % 3 = 1 := by
        have h11 : a % 3 = 1 := by omega
        simp [Nat.pow_mod, h11]
      have h12 : (7 * a ^ 2 + 8) % 3 = 0 := by
        have h12 : a ^ 2 % 3 = 1 := h11
        omega
      have h13 : ¬Nat.Prime (7 * a ^ 2 + 8) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (7 * a ^ 2 + 8) by omega)
        all_goals nlinarith
      contradiction
    · -- a % 3 = 2
      have h1' : a % 3 = 2 := by tauto
      have h11 : a ^ 2 % 3 = 1 := by
        have h11 : a % 3 = 2 := by omega
        simp [Nat.pow_mod, h11]
      have h12 : (8 * a ^ 2 + 7) % 3 = 0 := by
        have h12 : a ^ 2 % 3 = 1 := h11
        omega
      have h13 : ¬Nat.Prime (8 * a ^ 2 + 7) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * a ^ 2 + 7) by omega)
        all_goals nlinarith
      contradiction
  · -- Assume that a ≤ 3
    have ha1 : a = 2 ∨ a = 3 := by
      interval_cases a <;> try tauto
    rcases ha1 with (ha1 | ha1)
    · -- Assume that a = 2
      rw [ha1] at ha h7 h8
      norm_num at ha h7 h8
    · -- Assume that a = 3
      rw [ha1]
      constructor
      · norm_num
      · norm_num