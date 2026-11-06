import Mathlib

theorem number_theory_4935
    (a : ℤ) : 3 ∣ a^3 - a := by
  have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
    omega
  rcases h1 with (h | h | h)
  · 
    have h2 : a % 3 = 0 := h
    have h3 : (a ^ 3 - a) % 3 = 0 := by
      simp [Int.sub_emod, pow_two, pow_succ, h2, Int.add_emod, Int.mul_emod]
    omega
  · 
    have h2 : a % 3 = 1 := h
    have h3 : (a ^ 3 - a) % 3 = 0 := by
      simp [Int.sub_emod, pow_two, pow_succ, h2, Int.add_emod, Int.mul_emod]
    omega
  · 
    have h2 : a % 3 = 2 := h
    have h3 : (a ^ 3 - a) % 3 = 0 := by
      simp [Int.sub_emod, pow_two, pow_succ, h2, Int.add_emod, Int.mul_emod]
    omega