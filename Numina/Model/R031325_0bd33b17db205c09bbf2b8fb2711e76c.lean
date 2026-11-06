import Mathlib

theorem number_theory_114867 (x y : ℤ) : ¬(3 * x ^ 2 = 16 * y ^ 2 + 8 * y + 5) := by
  intro h
  have h1 : (3 * x ^ 2) % 8 = 5 := by
    have eq1 : (16 * y ^ 2 + 8 * y + 5) % 8 = 5 := by
      have h2 : (16 * y ^ 2 + 8 * y + 5) % 8 = 5 := by
        simp [Int.add_emod, Int.mul_emod, Int.sub_emod]
      assumption
    have eq2 : (3 * x ^ 2) % 8 = (16 * y ^ 2 + 8 * y + 5) % 8 := by
      omega
    rw [eq1] at eq2
    assumption
  have h2 : (3 * x ^ 2) % 8 = 0 ∨ (3 * x ^ 2) % 8 = 3 ∨ (3 * x ^ 2) % 8 = 4 := by
    have h3 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, h3] at *
  omega