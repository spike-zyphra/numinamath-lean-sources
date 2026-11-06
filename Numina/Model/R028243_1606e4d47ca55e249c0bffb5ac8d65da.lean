import Mathlib

theorem number_theory_1404 {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h1 : Nat.gcd x y = 4) (h2 : Nat.lcm x y = 20) :
    x^2 * y^2 + 3 * x * y + 1 = 6641 := by
  have h3 : x.gcd y * (x.lcm y) = x * y := by 
    rw [Nat.gcd_mul_lcm]
  rw [h1, h2] at h3
  have h4 : x * y = 80 := by
    nlinarith
  have h5 : x % 4 = 0 := by
    have h6 : 4 ∣ x := by
      have h1' : x.gcd y = 4 := h1
      have h7 : Nat.gcd x y ∣ x := by 
        apply Nat.gcd_dvd_left
      rw [h1'] at h7
      omega
    omega
  have h6 : y % 4 = 0 := by 
    have h1' : Nat.gcd x y = 4 := h1
    have h8 : Nat.gcd x y ∣ y := by 
      apply Nat.gcd_dvd_right
    rw [h1'] at h8
    omega
  have h5' : x ≤ 80 := by
    nlinarith [h4]
  have h6' : y ≤ 80 := by
    nlinarith [h4]
  have h7 : x = 4 ∨ x = 20 := by
    interval_cases x <;> norm_num at h4 h1 h2 ⊢ <;> try { 
      omega 
    }
  rcases h7 with h7 | h7
  · -- x = 4
    have h8 : y = 20 := by
      nlinarith [h4, h7]
    rw [h7, h8]
    all_goals norm_num
  · -- x = 20
    have h8 : y = 4 := by
      nlinarith [h4, h7]
    rw [h7, h8]
    all_goals norm_num