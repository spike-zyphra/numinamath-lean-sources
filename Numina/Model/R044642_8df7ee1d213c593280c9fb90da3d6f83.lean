import Mathlib

theorem algebra_300526 {a b c : ℤ} (ha : a ≠ 0) :
    (b^2 - 4 * a * c) ≠ 1986 := by 
  intro h
  have h1 : b^2 % 4 = 0 ∨ b^2 % 4 = 1 := by
    have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
      omega 
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h2]
  have h2 : (b ^ 2 - 4 * a * c) % 4 = 1986 % 4 := by 
    omega
  have h3 : (b ^ 2 - 4 * a * c) % 4 = 2 := by
    omega 
  have h4 : b^2 % 4 = 0 ∨ b^2 % 4 = 1 := h1 
  have h5 : (b ^ 2 - 4 * a * c) % 4 = b^2 % 4 := by
    have h6 : (4 * a * c) % 4 = 0 := by 
      simp [Int.mul_emod]
    omega 
  rw [h5] at h3 
  omega