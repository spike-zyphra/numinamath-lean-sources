import Mathlib

theorem number_theory_307605 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h1 : 10 + a = 12 + b) (h2 : 12 + b = 15 + c) (h3 : 15 + c = 10 + a) :
    a^2 + b^2 + c^2 - a * b - a * c - b * c = 19 := by
  have h4 : a = b + 2 := by 
    omega
  have h5 : c = b - 3 := by 
    omega
  have h6 : b = 5 := by
    by_cases h : b ≤ 20
    · -- if b ≤ 20
      interval_cases b <;> norm_num [h4] at ha
      <;> norm_num [h5] at hc
      <;> omega
    · -- if b > 20
      push_neg at h 
      have h7 : b % 2 = 0 ∨ b % 2 = 1 := by 
        omega
      rcases h7 with (h7 | h7)
      · -- b % 2 = 0 
        have h8 : b % 2 = 0 := by 
          omega
        have h9 : b > 2 := by 
          omega
        have h10 : ¬b.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ b by omega)
          all_goals omega
        contradiction
      · -- b % 2 = 1 
        have h8 : c % 2 = 0 := by
          omega
        have h9 : c > 2 := by 
          omega
        have h10 : ¬c.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ c by omega)
          all_goals omega
        contradiction
  have h7 : a = 7 := by 
    omega
  have h8 : c = 2 := by 
    omega
  calc
    a^2 + b^2 + c^2 - a * b - a * c - b * c 
        = 7^2 + 5^2 + 2^2 - 7 * 5 - 7 * 2 - 5 * 2 := by 
          rw [h7, h6, h8]
    _ = 49 + 25 + 4 - 35 - 14 - 10 := by 
      all_goals norm_num
    _ = 19 := by 
      all_goals norm_num