import Mathlib

theorem number_theory_144313 (k : ℤ) :
    ¬∃ x y, (8 * k + 3) = x ^ 2 - 2 * y ^ 2 ∨ (8 * k + 5) = x ^ 2 - 2 * y ^ 2 := by
  intro h
  rcases h with ⟨x, y, h⟩
  have h1 : (8 * k + 3) = x ^ 2 - 2 * y ^ 2 ∨ (8 * k + 5) = x ^ 2 - 2 * y ^ 2 := h
  rcases h1 with (h1 | h1)
  · -- Assume $8k + 3 = x^2 - 2y^2$
    have h2 : (x ^ 2 - 2 * y ^ 2) % 8 = 3 := by
      omega
    have h3 : (x ^ 2 % 8) = 0 ∨ (x ^ 2 % 8) = 1 ∨ (x ^ 2 % 8) = 4 := by
      have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
    have h4 : (y ^ 2 % 8) = 0 ∨ (y ^ 2 % 8) = 1 ∨ (y ^ 2 % 8) = 4 := by
      have h1 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
    omega
  · -- Assume $8k + 5 = x^2 - 2y^2$
    have h2 : (x ^ 2 - 2 * y ^ 2) % 8 = 5 := by
      omega
    have h3 : (x ^ 2 % 8) = 0 ∨ (x ^ 2 % 8) = 1 ∨ (x ^ 2 % 8) = 4 := by
      have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
    have h4 : (y ^ 2 % 8) = 0 ∨ (y ^ 2 % 8) = 1 ∨ (y ^ 2 % 8) = 4 := by
      have h1 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
    omega