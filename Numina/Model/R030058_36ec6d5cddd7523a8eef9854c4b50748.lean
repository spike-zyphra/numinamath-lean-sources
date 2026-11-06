import Mathlib

theorem number_theory_19388 : IsGreatest {p | ∃(m n : ℕ), 0 < m ∧ 0 < n ∧ m = 24 * n + 51 ∧ p = Nat.gcd (2 * m) (3 * n)} 102 := by 
  constructor
  · -- Show 102 is in the set
    use 867, 34
    all_goals norm_num 
  · -- Show that 102 is the greatest
    intro p hp
    rcases hp with ⟨m, n, hm, hn, hm_eq, hp_eq⟩
    rw [hp_eq] at *
    have h1 : Nat.gcd (2 * m) (3 * n) ∣ 2 * m := by 
      apply Nat.gcd_dvd_left 
    have h2 : Nat.gcd (2 * m) (3 * n) ∣ 3 * n := by 
      apply Nat.gcd_dvd_right 
    have h4 : Nat.gcd (2 * m) (3 * n) ∣ 102 := by
      have h111 : Nat.gcd (2 * m) (3 * n) ∣ (48 * n + 102 - 16 * (3 * n)) := by 
        apply Nat.dvd_sub' 
        · -- Nat.gcd (2 * m) (3 * n) divides 48 * n + 102
          have h112 : Nat.gcd (2 * m) (3 * n) ∣ 48 * n + 102 := by 
            have h113 : (48 * n + 102) = 2 * m := by 
              linarith [hm_eq]
            rw [h113] 
            exact h1 
          exact h112 
        · -- Nat.gcd (2 * m) (3 * n) divides 16 * (3 * n)
          have h114 : Nat.gcd (2 * m) (3 * n) ∣ 16 * (3 * n) := by 
            have h115 : Nat.gcd (2 * m) (3 * n) ∣ 3 * n := h2
            apply dvd_trans h115 
            all_goals norm_num 
          exact h114 
      have h102 : 48 * n + 102 - 16 * (3 * n) = 102 := by 
        omega 
      rw [h102] at h111 
      exact h111 
    have h5 : Nat.gcd (2 * m) (3 * n) ≤ 102 := by 
      exact Nat.le_of_dvd (by norm_num) h4 
    linarith