import Mathlib

theorem number_theory_5529 : IsGreatest {n | ∀ k, n ∣ (k * (k + 1) * (k + 2) * (k + 3))} 24 := by
  constructor
  · -- Show that 24 is in the set, i.e., for all k, 24 divides k*(k+1)*(k+2)*(k+3)
    intro k
    have h1 : k * (k + 1) * (k + 2) * (k + 3) % 24 = 0 := by
      have h2 : k % 24 = 0 ∨ k % 24 = 1 ∨ k % 24 = 2 ∨ k % 24 = 3 ∨ k % 24 = 4 ∨ k % 24 = 5 ∨ k % 24 = 6 ∨ k % 24 = 7 ∨ k % 24 = 8 ∨ k % 24 = 9 ∨ k % 24 = 10 ∨ k % 24 = 11 ∨ k % 24 = 12 ∨ k % 24 = 13 ∨ k % 24 = 14 ∨ k % 24 = 15 ∨ k % 24 = 16 ∨ k % 24 = 17 ∨ k % 24 = 18 ∨ k % 24 = 19 ∨ k % 24 = 20 ∨ k % 24 = 21 ∨ k % 24 = 22 ∨ k % 24 = 23 := by
        omega
      rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod]
      <;> omega
    exact Nat.dvd_of_mod_eq_zero h1
  · -- Show that 24 is the greatest such integer
    intro n hn
    have h2 := hn 1
    have h1 : n ∣ (1 * (1 + 1) * (1 + 2) * (1 + 3)) := h2
    have h24 : n ∣ 24 := by
      norm_num at h1
      exact h1
    have h3 : n ≤ 24 := by
      exact Nat.le_of_dvd (by norm_num) h24
    linarith