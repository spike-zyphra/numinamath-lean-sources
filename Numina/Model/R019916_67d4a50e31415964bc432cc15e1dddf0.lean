import Mathlib

theorem algebra_275914 (x : ℤ) (hx : Odd x) : 48 ∣ x^3 + 3 * x^2 - x - 3 := by
  have h1 : x % 2 = 1 := by 
    rcases hx with ⟨k, hk⟩
    omega
  have h3 : (x^3 + 3 * x^2 - x - 3) % 3 = 0 := by
    have h2 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · 
      simp [h2, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      simp [h2, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      simp [h2, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
  have h4 : (x^3 + 3 * x^2 - x - 3) % 16 = 0 := by
    have h5 : x % 2 = 1 := h1
    have h6 : x % 16 = 1 ∨ x % 16 = 3 ∨ x % 16 = 5 ∨ x % 16 = 7 ∨ x % 16 = 9 ∨ x % 16 = 11 ∨ x % 16 = 13 ∨ x % 16 = 15 := by
      omega
    rcases h6 with (h | h | h | h | h | h | h | h)
    · 
      simp [h, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      simp [h, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      simp [h, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      simp [h, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      simp [h, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      simp [h, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      simp [h, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
    · 
      simp [h, pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
  omega