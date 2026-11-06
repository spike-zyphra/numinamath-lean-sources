import Mathlib

theorem number_theory_12103 (a b : ℕ) (h₀ : Nat.gcd a b * Nat.lcm a b = 180) :
    Nat.gcd a b = 1 ∨ Nat.gcd a b = 2 ∨ Nat.gcd a b = 3 ∨ Nat.gcd a b = 6 := by 
  have h1 : a * b = 180 := by 
    have h2 : Nat.gcd a b * Nat.lcm a b = a * b := by 
      rw [Nat.gcd_mul_lcm]
    linarith [h₀, h2]
  have h2 : a ∣ 180 := by 
    use b
    all_goals nlinarith [h1]
  have h3 : b ∣ 180 := by 
    use a
    all_goals nlinarith [h1]
  have h4 : a ≤ 180 := by 
    exact Nat.le_of_dvd (by norm_num) h2
  have h5 : b ≤ 180 := by 
    exact Nat.le_of_dvd (by norm_num) h3
  interval_cases a <;> try { 
    omega 
  } 
  <;> try { 
    interval_cases b <;> norm_num at h1 
    <;> norm_num [Nat.gcd] at h₀ ⊢ 
    <;> omega 
  }