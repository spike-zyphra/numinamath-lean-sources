import Mathlib

theorem number_theory_11389 :
    IsGreatest {x | ∃ n : ℕ, 0 < n ∧ x = Nat.gcd (11 * n + 3) (6 * n + 1)} 7 := by
  constructor
  · -- Show that 7 is in the set
    use 1
    constructor
    · norm_num
    · norm_num
  · -- Show that 7 is greatest in the set
    intro x h
    rcases h with ⟨n, hn, hx⟩
    rw [hx]
    have h1 : Nat.gcd (11 * n + 3) (6 * n + 1) ∣ (11 * n + 3) := by
      exact Nat.gcd_dvd_left (11 * n + 3) (6 * n + 1)
    have h2 : Nat.gcd (11 * n + 3) (6 * n + 1) ∣ (6 * n + 1) := by
      exact Nat.gcd_dvd_right (11 * n + 3) (6 * n + 1)
    have h3 : Nat.gcd (11 * n + 3) (6 * n + 1) ∣ 7 := by
      have h4 : Nat.gcd (11 * n + 3) (6 * n + 1) ∣ (6 * (11 * n + 3)) := by
        apply dvd_trans h1
        norm_num
      have h5 : Nat.gcd (11 * n + 3) (6 * n + 1) ∣ (11 * (6 * n + 1)) := by
        apply dvd_trans h2
        norm_num
      have h6 : Nat.gcd (11 * n + 3) (6 * n + 1) ∣ (6 * (11 * n + 3) - 11 * (6 * n + 1)) := by
        apply Nat.dvd_sub'
        · -- Show that gcd (11 * n + 3) (6 * n + 1) divides 6 * (11 * n + 3)
          exact h4
        · -- Show that gcd (11 * n + 3) (6 * n + 1) divides 11 * (6 * n + 1)
          exact h5
      have h7 : 6 * (11 * n + 3) - 11 * (6 * n + 1) = 7 := by
        omega
      rw [h7] at h6
      exact h6
    have h4 : Nat.gcd (11 * n + 3) (6 * n + 1) ≤ 7 := by
      exact Nat.le_of_dvd (by norm_num) h3
    linarith