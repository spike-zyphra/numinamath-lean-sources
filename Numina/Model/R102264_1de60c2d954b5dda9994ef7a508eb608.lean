import Mathlib

theorem algebra_101949 (m n : ℤ) :
    m^3 + 6 * m^2 + 5 * m = 27 * n^3 + 9 * n^2 + 9 * n + 1 ↔ False := by
  constructor
  · -- Assume the equation holds, prove False
    intro h
    have h1 : m^3 + 6 * m^2 + 5 * m = 27 * n^3 + 9 * n^2 + 9 * n + 1 := h
    have h2 : (m^3 + 6 * m^2 + 5 * m) % 3 = (27 * n^3 + 9 * n^2 + 9 * n + 1) % 3 := by
      omega
    have h3 : (m^3 + 6 * m^2 + 5 * m) % 3 = 0 := by 
      have h4 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by 
        omega
      rcases h4 with (h4 | h4 | h4)
      · 
        simp [pow_succ, Int.mul_emod, Int.add_emod, Int.mul_emod, h4, Int.sub_emod]
        all_goals ring_nf <;> omega
      · 
        simp [pow_succ, Int.mul_emod, Int.add_emod, Int.mul_emod, h4, Int.sub_emod]
        all_goals ring_nf <;> omega
      · 
        simp [pow_succ, Int.mul_emod, Int.add_emod, Int.mul_emod, h4, Int.sub_emod]
        all_goals ring_nf <;> omega
    have h4 : (27 * n^3 + 9 * n^2 + 9 * n + 1) % 3 = 1 := by
      omega
    omega
  · -- Assume False, prove the equation
    intro h
    cases h