import Mathlib

theorem number_theory_167981 (a b : ℤ) (_ : 0 < a) (hb : 0 < b)
    (hpa : a % 2 ≠ b % 2) :
    ¬ ∃ x, x^2 = (a + 3 * b) * (5 * a + 7 * b) := by 
  rintro ⟨x, hx⟩ 
  have h1 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by 
    have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h) <;> 
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h] at *
  have h2 : (a + 3 * b) * (5 * a + 7 * b) % 8 = 5 := by 
    have h2 : (a % 2 = 0 ∧ b % 2 = 1) ∨ (a % 2 = 1 ∧ b % 2 = 0) := by 
      omega 
    rcases h2 with (h | h)
    · -- case where a is even and b is odd 
      have ha0 : a % 2 = 0 := h.1
      have hb1 : b % 2 = 1 := h.2
      have h3 : a % 8 = 0 ∨ a % 8 = 2 ∨ a % 8 = 4 ∨ a % 8 = 6 := by 
        omega 
      have h4 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by 
        omega 
      rcases h3 with (h3 | h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4 | h4) <;> 
        norm_num [Int.add_emod, Int.mul_emod, h3, h4] at *
    · -- case where a is odd and b is even 
      have ha1 : a % 2 = 1 := h.1
      have hb0 : b % 2 = 0 := h.2
      have h3 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by 
        omega 
      have h4 : b % 8 = 0 ∨ b % 8 = 2 ∨ b % 8 = 4 ∨ b % 8 = 6 := by 
        omega 
      rcases h3 with (h3 | h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4 | h4) <;> 
        norm_num [Int.add_emod, Int.mul_emod, h3, h4] at *
  have h3 : (a + 3 * b) * (5 * a + 7 * b) % 8 = 5 := h2 
  have h4 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := h1 
  have h5 : (a + 3 * b) * (5 * a + 7 * b) % 8 = x^2 % 8 := by 
    omega 
  omega