import Mathlib

theorem algebra_10704 : IsGreatest {p | p.Prime ∧ p ∣ (15 ^ 4 + 2 * 15 ^ 2 + 1 - 14 ^ 4)} 211 := by
  have h : 15 ^ 4 + 2 * 15 ^ 2 + 1 - 14 ^ 4 = 12660 := by
    norm_num
  rw [h] at *
  constructor
  · -- Show that 211 is in the set
    constructor
    · -- Show 211 is prime
      norm_num
    · -- Show 211 divides 12660
      norm_num
  · -- Show that if p is in the set, p ≤ 211
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    by_contra h
    push_neg at h
    have h1 : p ≤ 12660 := by 
      exact Nat.le_of_dvd (by norm_num) h_div
    have h9 : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 211 := by
      have h10 : p ∣ 12660 := h_div
      have h11 : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 211 := by
        have h10 : p ∣ 12660 := h_div
        have h12 : 12660 = 2 * (2 * 3 * 5 * 211) := by
          norm_num
        rw [h12] at h10
        have h13 : p ∣ 2 ∨ p ∣ (2 * 3 * 5 * 211) := (Nat.Prime.dvd_mul h_prime).mp h10
        rcases h13 with (h | h)
        · left
          exact h
        · have h14 : p ∣ 2 ∨ p ∣ (3 * 5 * 211) := (Nat.Prime.dvd_mul h_prime).mp h
          rcases h14 with (h | h)
          · left
            exact h
          · have h15 : p ∣ 3 ∨ p ∣ (5 * 211) := (Nat.Prime.dvd_mul h_prime).mp h
            rcases h15 with (h | h)
            · right
              left
              exact h
            · have h16 : p ∣ 5 ∨ p ∣ 211 := (Nat.Prime.dvd_mul h_prime).mp h
              rcases h16 with (h | h)
              · right
                right
                left
                exact h
              · right
                right
                right
                exact h
      exact h11
    rcases h9 with (h | h | h | h)
    · -- The case where p|2, then p = 2 false with h p > 211
      have : p ≤ 2 := by
        have : p ∣ 2 := h
        exact Nat.le_of_dvd (by norm_num) this
      linarith
    · -- The case where p|3, then p = 3 false with h p > 211
      have : p ≤ 3 := by
        have : p ∣ 3 := h
        exact Nat.le_of_dvd (by norm_num) this
      linarith
    · -- The case where p|5, then p = 5 false with h p > 211
      have : p ≤ 5 := by
        have : p ∣ 5 := h
        exact Nat.le_of_dvd (by norm_num) this
      linarith
    · -- The case where p|211, then p = 211 false with h p > 211
      have : p ≤ 211 := by
        have : p ∣ 211 := h
        exact Nat.le_of_dvd (by norm_num) this
      linarith