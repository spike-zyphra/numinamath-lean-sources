import Mathlib

theorem algebra_284685 :
    IsGreatest {n | 0 < n ∧ (n + 26) ∣ n^3 + 2006} 15544 := by
  constructor
  · -- Show 15544 is in the set
    constructor
    · -- Show 0 < 15544
      norm_num
    · -- Show (15544 + 26) ∣ 15544^3 + 2006
      norm_num
  · -- Show 15544 is greatest
    intro n hn
    rcases hn with ⟨hn_pos, hdiv⟩
    have h1 : (n + 26) ∣ n^3 + 2006 := hdiv
    have h2 : (n + 26) ∣ 15570 := by
      have h3 : (n + 26 : ℤ) ∣ (n^3 + 2006 : ℤ) := by
        exact_mod_cast hdiv
      have h4 : (n + 26 : ℤ) ∣ 15570 := by
        have h14 : (n + 26 : ℤ) ∣ ((n^3 + 2006 : ℤ) + 15570) := by
          have eq3 : ((n^3 + 2006 : ℤ) + 15570) = ((n + 26 : ℤ) * ((n : ℤ)^2 - 26 * (n : ℤ) + 676 : ℤ)) := by 
            ring
          rw [eq3]
          apply dvd_mul_right
        have eq5 : (n + 26 : ℤ) ∣ ((n^3 + 2006 + 15570 : ℤ) - (n^3 + 2006 : ℤ)) := by
          apply Dvd.dvd.sub
          exact h14
          exact h3
        have eq6 : ((n^3 + 2006 + 15570 : ℤ) - (n^3 + 2006 : ℤ)) = (15570 : ℤ) := by
          omega
        rw [eq6] at eq5
        exact_mod_cast eq5
      exact_mod_cast h4
    have h3' : (n + 26) ∣ 15570 := h2
    have h4 : (n + 26) ≤ 15570 := by 
      exact Nat.le_of_dvd (by omega) h3'
    have h5 : n ≤ 15544 := by
      omega
    linarith