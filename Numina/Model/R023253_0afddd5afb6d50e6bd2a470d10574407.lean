import Mathlib


theorem number_theory_6490 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.gcd a b = 10) (h : Nat.lcm a b = 100) :
    (a, b) = (10, 100) ∨ (a, b) = (100, 10) ∨
    (a, b) = (20, 50) ∨ (a, b) = (50, 20) := by

  have h1 : a.gcd b * a.lcm b = a * b := by
    exact Nat.gcd_mul_lcm a b

  rw [hab, h] at h1

  have h2 : a * b = 1000 := by
    nlinarith

  have h3 : 10 ∣ a := by 
    have h3 : Nat.gcd a b ∣ a := by 
      exact Nat.gcd_dvd_left a b
    rw [hab] at h3
    exact h3

  have h4 : 10 ∣ b := by 
    have h4 : Nat.gcd a b ∣ b := by 
      exact Nat.gcd_dvd_right a b
    rw [hab] at h4
    exact h4

  rcases h3 with ⟨x, hx⟩
  rcases h4 with ⟨y, hy⟩
  have h5 : x * y = 10 := by
    nlinarith [h2, hx, hy]

  have h6 : Nat.gcd x y = 1 := by 
    have h7 : Nat.gcd a b = 10 * Nat.gcd x y := by
      rw [show a = 10 * x by linarith [hx], show b = 10 * y by linarith [hy]]
      simp [Nat.gcd_mul_left]
    rw [hab] at h7
    omega

  have h7 : x ≤ 10 := by
    have h7 : x ∣ 10 := by
      use y
      all_goals nlinarith [h5]
    have h8 : x ≤ 10 := by
      exact Nat.le_of_dvd (by norm_num) h7
    exact h8

  interval_cases x <;> norm_num [Prod.ext_iff, hx, hy] at *
  all_goals
    omega