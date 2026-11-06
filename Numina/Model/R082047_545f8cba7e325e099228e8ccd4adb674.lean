import Mathlib

theorem number_theory_14882
    {n : ℕ}
    (hn : 0 < n)
    (h1 : Nat.lcm 24 n = 72)
    (h2 : Nat.lcm n 27 = 108) :
    n = 36 := by

  have h6 : n ∣ 72 := by
    have h : n ∣ 72 := by
      rw [← h1]
      apply Nat.dvd_lcm_right
    exact h
  have h7 : n ∣ 108 := by
    have h : n ∣ 108 := by
      rw [← h2]
      apply Nat.dvd_lcm_left
    exact h
  have h8 : n ∣ 36 := by 
      exact Nat.dvd_gcd h6 h7
  have h5 : n ≤ 36 := by 
    exact Nat.le_of_dvd (by positivity) h8
  interval_cases n <;> norm_num [Nat.lcm] at h1 h2 ⊢ <;> all_goals
    omega