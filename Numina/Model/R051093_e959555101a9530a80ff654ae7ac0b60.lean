import Mathlib

theorem algebra_275899 (a : ℤ) : 24 ∣ (a^2 + 3 * a + 1)^2 - 1 := by
  have h1 : (a ^ 2 + 3 * a + 1) ^ 2 - 1 = ((a ^ 2 + 3 * a + 1) - 1) * ((a ^ 2 + 3 * a + 1) + 1) := by 
    ring
  rw [h1]
  have h2 : ((a ^ 2 + 3 * a + 1) - 1) * ((a ^ 2 + 3 * a + 1) + 1) % 8 = 0 := by 
    have h3 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
      omega
    rcases h3 with (h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h3 : ((a ^ 2 + 3 * a + 1) - 1) * ((a ^ 2 + 3 * a + 1) + 1) % 3 = 0 := by 
    have h4 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
      omega 
    rcases h4 with (h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h4 : 24 ∣ ((a ^ 2 + 3 * a + 1) - 1) * ((a ^ 2 + 3 * a + 1) + 1) := by 
    omega
  exact h4