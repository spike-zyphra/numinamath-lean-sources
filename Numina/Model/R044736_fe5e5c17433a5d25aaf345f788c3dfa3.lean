import Mathlib

theorem number_theory_281776 (a : ℤ) : 6 ∣ a^3 + 11 * a := by
  have h1 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by 
    omega
  rcases h1 with (h | h | h | h | h | h)
  · 
    have h2 : (a ^ 3 + 11 * a) % 6 = 0 := by 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  · 
    have h2 : (a ^ 3 + 11 * a) % 6 = 0 := by 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  · 
    have h2 : (a ^ 3 + 11 * a) % 6 = 0 := by 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  · 
    have h2 : (a ^ 3 + 11 * a) % 6 = 0 := by 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  · 
    have h2 : (a ^ 3 + 11 * a) % 6 = 0 := by 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  · 
    have h2 : (a ^ 3 + 11 * a) % 6 = 0 := by 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    omega