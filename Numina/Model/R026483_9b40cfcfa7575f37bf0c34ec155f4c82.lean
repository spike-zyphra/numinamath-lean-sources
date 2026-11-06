import Mathlib

theorem number_theory_210506 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h_lcm : Nat.lcm a b = 165) (h_gcd : Nat.gcd a b = 5) :
    a + b ≤ 170 := by 
  have h3 : a * b = 5 * 165 := by 
    calc 
      a * b = (Nat.gcd a b) * (Nat.lcm a b) := by rw [Nat.gcd_mul_lcm]
      _ = 5 * 165 := by rw [h_gcd, h_lcm]
  have h4 : a ≤ 165 := by
    have h5 : a ∣ 165 := by
      have h6 : Nat.lcm a b = 165 := h_lcm
      have h7 : a ∣ Nat.lcm a b := Nat.dvd_lcm_left a b
      rw [h6] at h7
      exact h7
    exact Nat.le_of_dvd (by norm_num) h5
  have h5 : b ≤ 165 := by
    have h6 : b ∣ 165 := by
      have h7 : Nat.lcm a b = 165 := h_lcm
      have h8 : b ∣ Nat.lcm a b := Nat.dvd_lcm_right a b
      rw [h7] at h8
      exact h8
    exact Nat.le_of_dvd (by norm_num) h6
  have h8 : a % 5 = 0 := by
    -- We know that GCD(a, b) = 5, so 5 divides a and b.
    have h9 : Nat.gcd a b = 5 := h_gcd
    have h10 : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
    rw [h9] at h10
    have h50 : 5 ∣ a := by 
      exact h10
    have h51 : a % 5 = 0 := by
      omega
    exact h51
  interval_cases a <;> norm_num at h3 h4 h5 h8 ⊢
  <;> try { 
    all_goals
      have h9 : b ≤ 165 := by
        have h4 : b ∣ 165 := by
          have h1 : Nat.lcm a b = 165 := h_lcm 
          have : b ∣ Nat.lcm a b := Nat.dvd_lcm_right a b 
          rw [h1] at this 
          exact this 
        exact Nat.le_of_dvd (by norm_num) h4
      interval_cases b <;> norm_num at h3 h4 h5 h8 h9 ⊢ 
      <;> omega
    <;> omega
  }
  <;> omega