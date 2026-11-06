import Mathlib

theorem number_theory_38027 {a b : ℕ} (hab : a.gcd b = 12 ∧ Nat.lcm a b = 168) :
    a * b = 2016 := by 
  have h1 : a.gcd b = 12 := hab.left
  have h2 : Nat.lcm a b = 168 := hab.right
  calc 
    a * b = a.gcd b * a.lcm b := by rw [Nat.gcd_mul_lcm]
    _ = 12 * 168 := by rw [h1, h2]
    _ = 2016 := by norm_num