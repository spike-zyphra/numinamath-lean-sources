import Mathlib

theorem algebra_300985 (n : ℤ) (hn : n > 0) :
    ¬ ∃ m, m^2 = n^6 + 3 * n^5 - 9 * n^4 - 11 * n^3 + 8 * n^2 + 12 * n + 3 := by 
  rintro ⟨m, hm⟩
  have h1 : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
      omega 
    rcases h1 with (h1 | h1 | h1 | h1) <;> simp [sq, Int.add_emod, Int.mul_emod, h1, pow_two]
  have h2 : (n ^ 6 + 3 * n ^ 5 - 9 * n ^ 4 - 11 * n ^ 3 + 8 * n ^ 2 + 12 * n + 3) % 4 = 3 := by
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by 
      omega
    rcases h2 with (h2 | h2)
    · 
      have h3 : n % 4 = 0 ∨ n % 4 = 2 := by 
        omega 
      rcases h3 with (h3 | h3)
      · 
        have h4 : n % 4 = 0 := h3
        simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ, pow_zero, h4, Int.add_emod, Int.sub_emod, Int.mul_emod]
      · 
        have h4 : n % 4 = 2 := h3
        simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ, pow_zero, h4, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      have h3 : n % 4 = 1 ∨ n % 4 = 3 := by
        omega 
      rcases h3 with (h3 | h3)
      · 
        have h4 : n % 4 = 1 := h3
        simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ, pow_zero, h4, Int.add_emod, Int.sub_emod, Int.mul_emod]
      · 
        have h4 : n % 4 = 3 := h3
        simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ, pow_zero, h4, Int.add_emod, Int.sub_emod, Int.mul_emod]
  have h6 : m ^ 2 = n^6 + 3 * n^5 - 9 * n^4 - 11 * n^3 + 8 * n^2 + 12 * n + 3 := hm
  have h7 : m ^ 2 % 4 = 3 := by
    omega
  omega