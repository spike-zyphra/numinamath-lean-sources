import Mathlib

theorem number_theory_198560 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (d v : ℕ) (hd : d = Nat.gcd a b) (hv : v = Nat.lcm a b) :
    a + b ≤ d + v := by 
  rw [hd, hv]
  have h1 : a.gcd b ∣ a := by 
    apply Nat.gcd_dvd_left 
  have h2 : a.gcd b ∣ b := by 
    apply Nat.gcd_dvd_right 
  have h3 : a.gcd b * a.lcm b = a * b := by 
    rw [Nat.gcd_mul_lcm] 
  have h4 : a * b = a.gcd b * a.lcm b := by 
    linarith [h3] 
  have h5 : a.gcd b ≤ a := by 
    apply Nat.gcd_le_left 
    all_goals omega 
  have h6 : a.gcd b ≤ b := by 
    apply Nat.gcd_le_right 
    all_goals omega 
  have h7 : a ≤ a.lcm b := by 
    have h8 : a ∣ a.lcm b := by 
      apply Nat.dvd_lcm_left 
    have h9 : 0 < a := by 
      omega 
    have h10 : 0 < a.lcm b := by 
      apply Nat.lcm_pos 
      all_goals omega 
    exact Nat.le_of_dvd (by omega) h8 
  have h8 : b ≤ a.lcm b := by 
    have h9 : b ∣ a.lcm b := by 
      apply Nat.dvd_lcm_right 
    have h10 : 0 < b := by 
      omega 
    have h11 : 0 < a.lcm b := by 
      apply Nat.lcm_pos 
      all_goals omega 
    exact Nat.le_of_dvd (by omega) h9 
  nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a - a.gcd b : ℤ), sq_nonneg (b - a.gcd b : ℤ),
          sq_nonneg ((a.lcm b : ℤ) - a : ℤ), sq_nonneg ((a.lcm b : ℤ) - b : ℤ), 
          sq_nonneg ((a.gcd b : ℤ) - (a.lcm b : ℤ)), 
          mul_pos (show 0 < a by omega) (show 0 < b by omega), 
          Nat.gcd_pos_of_pos_left b (show 0 < a by omega), 
          mul_pos (show 0 < a by omega) (show 0 < b by omega)]