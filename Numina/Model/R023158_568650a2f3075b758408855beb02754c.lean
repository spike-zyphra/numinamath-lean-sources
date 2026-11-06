import Mathlib

theorem number_theory_4321 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a.gcd b = 12) (h2 : a.lcm b = 504)
    (h3 : a + b < 200) : a + b = 156 := by
  have h4 : a.gcd b * (a.lcm b) = a * b := by
    rw [Nat.gcd_mul_lcm]
  -- From h1 and h2: 12 * 504 = a * b
  have h5 : a * b = 6048 := by 
    calc
      a * b = a.gcd b * (a.lcm b) := by 
        rw [h4]
      _ = 12 * 504 := by 
        rw [h1, h2]
      _ = 6048 := by 
        norm_num 
  -- From h1, we know that a and b are multiples of 12
  have h7' : a % 12 = 0 := by 
    have h8 : a.gcd b ∣ a := by 
      exact Nat.gcd_dvd_left a b 
    have h10 : a.gcd b = 12 := h1 
    have h11 : 12 ∣ a := by 
      rw [h10] at h8 
      exact h8 
    have h12 : a % 12 = 0 := by 
      omega 
    exact h12 
  -- Similarly to b: 
  have h8' : b % 12 = 0 := by 
    have h9 : a.gcd b ∣ b := by 
      exact Nat.gcd_dvd_right a b 
    have h10 : a.gcd b = 12 := h1 
    have h11 : 12 ∣ b := by 
      rw [h10] at h9 
      exact h9 
    have h12 : b % 12 = 0 := by 
      omega 
    exact h12 
  have h9 : a = 12 * (a / 12) := by 
    omega 
  have h10 : b = 12 * (b / 12) := by 
    omega 
  rw [h9, h10] at h5 
  -- Now writing h5: $12 \cdot 12 \cdot (a / 12) \cdot (b / 12) = 6048$.
  -- Solving further: 144 * (a / 12) * (b / 12) = 6048
  -- Therefore: (a / 12) * (b / 12) = 42
  have h11 : (a / 12) * (b / 12) = 42 := by
    nlinarith [h5]
  -- Now writing from h1: a.gcd b = 12, and a = 12 * (a / 12) and b = 12 * (b / 12)
  -- Then we have that Nat.gcd (a) (b) = 12 * Nat.gcd (a / 12) (b / 12)
  -- Solving further, Nat.gcd (a / 12) (b / 12) = 1
  have h12 : Nat.gcd (a / 12) (b / 12) = 1 := by
    have h6 : Nat.gcd (a) (b) = 12 := h1 
    -- From the fact that a.gcd b = 12, and a = 12 * x, b = 12 * y, we have that gcd(x, y) = 1
    have h9 : a = 12 * (a / 12) := h9 
    have h10 : b = 12 * (b / 12) := h10 
    have h11 : Nat.gcd (a) (b) = 12 * Nat.gcd (a / 12) (b / 12) := by 
      rw [h9, h10] 
      simp [Nat.gcd_mul_left]
    rw [h6] at h11 
    omega 
  have h14 : (a / 12) ∣ 42 := by 
    use (b / 12) 
    linarith [h11] 
  have h15 : (a / 12) ≤ 42 := by 
    exact Nat.le_of_dvd (by norm_num) h14 
  interval_cases h : (a / 12) <;> 
    omega 
  all_goals 
    try { 
      omega 
    } 
    <;> try { 
      norm_num at h11 h12 
      try { 
        omega 
      } 
    }