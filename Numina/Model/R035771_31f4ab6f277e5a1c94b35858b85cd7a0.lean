import Mathlib

theorem number_theory_113391 (a : ℕ) :
    IsGreatest {n | n ∣ 8 * a + 3 ∧ n ∣ 5 * a + 2} 1 := by
  constructor
  · -- Show that 1 is in the set
    constructor
    · -- 1 divides 8 * a + 3
      simp
    · -- 1 divides 5 * a + 2
      simp
  · -- Show that 1 is greatest in the set
    intro n hn
    rcases hn with ⟨h1, h2⟩
    have h3 : n ∣ 1 := by
      have h4 : n ∣ 8 * a + 3 := h1
      have h5 : n ∣ 5 * a + 2 := h2
      -- n divides 1, since 1 = 8*(5a+2) -5*(8a+3)
      have h6 : n ∣ (8 * (5 * a + 2)) := by
        apply dvd_trans h5 
        simp
      have h7 : n ∣ (5 * (8 * a + 3)) := by 
        apply dvd_trans h1 
        simp
      have h8 : n ∣ ((8 * (5 * a + 2)) - (5 * (8 * a + 3))) := by 
        apply Nat.dvd_sub'
        · -- Show that n divides 8*(5a+2)
          exact h6
        · -- Show that n divides 5*(8a+3)
          exact h7
      have h9 : ((8 * (5 * a + 2)) - (5 * (8 * a + 3))) = 1 := by
        omega
      rw [h9] at h8 
      exact h8 
    have h4 : n ≤ 1 := by 
      exact Nat.le_of_dvd (by norm_num) h3
    linarith