import Mathlib

theorem number_theory_215557 (n : ℤ) : 6 ∣ n * (n ^ 2 + 5) := by 
  have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by 
    omega 
  rcases h1 with (h | h | h | h | h | h)
  · 
    have h2 : n % 6 = 0 := h 
    have h3 : (n * (n ^ 2 + 5)) % 6 = 0 := by 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2] 
    omega 
  · 
    have h2 : n % 6 = 1 := h 
    have h3 : (n * (n ^ 2 + 5)) % 6 = 0 := by 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2] 
    omega 
  · 
    have h2 : n % 6 = 2 := h 
    have h3 : (n * (n ^ 2 + 5)) % 6 = 0 := by 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2] 
    omega 
  · 
    have h2 : n % 6 = 3 := h 
    have h3 : (n * (n ^ 2 + 5)) % 6 = 0 := by 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2] 
    omega 
  · 
    have h2 : n % 6 = 4 := h 
    have h3 : (n * (n ^ 2 + 5)) % 6 = 0 := by 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2] 
    omega 
  · 
    have h2 : n % 6 = 5 := h 
    have h3 : (n * (n ^ 2 + 5)) % 6 = 0 := by 
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2] 
    omega