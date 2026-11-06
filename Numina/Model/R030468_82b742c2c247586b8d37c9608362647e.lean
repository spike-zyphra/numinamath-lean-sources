import Mathlib

theorem number_theory_254887 (a : ℤ) : 60 ∣ (a^2 - 1) * a^2 * (a^2 + 1) := by
  have h1 : (a ^ 2 - 1) * a ^ 2 * (a ^ 2 + 1) % 3 = 0 := by
    have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases h1 with (h1 | h1 | h1) <;> simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h2 : (a ^ 2 - 1) * a ^ 2 * (a ^ 2 + 1) % 4 = 0 := by
    have h2 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [h2, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h3 : (a ^ 2 - 1) * a ^ 2 * (a ^ 2 + 1) % 5 = 0 := by
    have h3 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3) <;> simp [h3, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
  omega