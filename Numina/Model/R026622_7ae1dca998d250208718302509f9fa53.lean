import Mathlib

theorem number_theory_202620 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    10 ∣ a^3 * b - a * b^3 ∨ 10 ∣ b^3 * c - b * c^3 ∨ 10 ∣ c^3 * a - c * a^3 := by 
  have h4 : (a^3 * b - a * b^3) % 2 = 0 := by
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by 
      omega
    have h2 : b % 2 = 0 ∨ b % 2 = 1 := by 
      omega
    rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2)
      <;> simp [h1, h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
  have h5 : (b^3 * c - b * c^3) % 2 = 0 := by 
    have h2 : b % 2 = 0 ∨ b % 2 = 1 := by 
      omega
    have h3 : c % 2 = 0 ∨ c % 2 = 1 := by 
      omega
    rcases h2 with (h2 | h2) <;> rcases h3 with (h3 | h3)
      <;> simp [h2, h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
  have h6 : (c^3 * a - c * a^3) % 2 = 0 := by 
    have h3 : c % 2 = 0 ∨ c % 2 = 1 := by 
      omega
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by 
      omega
    rcases h3 with (h3 | h3) <;> rcases h1 with (h1 | h1)
      <;> simp [h3, h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
  have h7 : (a^3 * b - a * b^3) % 5 = 0 ∨ (b^3 * c - b * c^3) % 5 = 0 ∨ (c^3 * a - c * a^3) % 5 = 0 := by
    have h8 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
      omega
    have h9 : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by
      omega
    have h10 : c % 5 = 0 ∨ c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by
      omega
    rcases h8 with (h8 | h8 | h8 | h8 | h8) <;> rcases h9 with (h9 | h9 | h9 | h9 | h9) <;> 
      rcases h10 with (h10 | h10 | h10 | h10 | h10) <;> 
        simp [h8, h9, h10, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
        <;> omega
  rcases h7 with (h7 | h7 | h7)
  · 
    omega
  · 
    omega
  · 
    omega