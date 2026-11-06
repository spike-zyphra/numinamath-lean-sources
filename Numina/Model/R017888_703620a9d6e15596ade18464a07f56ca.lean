import Mathlib

theorem number_theory_4699 (n : ℕ) (hn : n > 0) :
    Nat.gcd n (n + 10) = 1 ∨ Nat.gcd n (n + 10) = 2 ∨ Nat.gcd n (n + 10) = 5 ∨ Nat.gcd n (n + 10) = 10 := by
  -- Let h1 = gcd n (n + 10)
  -- We know h1 divides n
  have h1 : Nat.gcd n (n + 10) ∣ n := by
    exact Nat.gcd_dvd_left n (n + 10)
  -- We know h1 divides n + 10
  have h2 : Nat.gcd n (n + 10) ∣ (n + 10) := by
    exact Nat.gcd_dvd_right n (n + 10)
  -- So h1 divides (n + 10) - n = 10
  have h3 : Nat.gcd n (n + 10) ∣ 10 := by
    have h4 : Nat.gcd n (n + 10) ∣ (n + 10) := by
      exact Nat.gcd_dvd_right n (n + 10)
    have h5 : Nat.gcd n (n + 10) ∣ n := by
      exact Nat.gcd_dvd_left n (n + 10)
    have h6 : Nat.gcd n (n + 10) ∣ ((n + 10) - n) := by
      apply Nat.dvd_sub'
      · exact h4
      · exact h5
    have h7 : ((n + 10) - n) = 10 := by
      omega
    rw [h7] at h6
    exact h6
  -- Therefore h1 ≤ 10
  have h4 : Nat.gcd n (n + 10) ≤ 10 := by
    exact Nat.le_of_dvd (by norm_num) h3
  -- Now, we can use interval_cases to prove it
  interval_cases h : Nat.gcd n (n + 10) <;> norm_num at h1 h2 h3 h4 h
  <;> omega