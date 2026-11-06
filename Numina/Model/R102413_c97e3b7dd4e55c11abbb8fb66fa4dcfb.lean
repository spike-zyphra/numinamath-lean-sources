import Mathlib

theorem number_theory_5802 :
    IsGreatest {d : ℕ | ∃ a b, a > 0 ∧ b > 0 ∧ a - b = 2019 ∧ d = Nat.gcd a b} 2019 := by
  constructor
  · -- Show that 2019 is achievable
    use 4038, 2019
    all_goals norm_num
  · -- Show that no greater element exists
    intro d
    rintro ⟨a, b, ha, hb, hab, hdb⟩
    have h1 : d ∣ a := by
      rw [hdb]
      exact Nat.gcd_dvd_left a b
    have h2 : d ∣ b := by
      rw [hdb]
      exact Nat.gcd_dvd_right a b
    have h3 : d ∣ (a - b) := by
      apply Nat.dvd_sub'
      · exact h1
      · exact h2
    rw [show a - b = 2019 by omega] at h3
    have h4 : d ≤ 2019 := by
      exact Nat.le_of_dvd (by norm_num) h3
    linarith