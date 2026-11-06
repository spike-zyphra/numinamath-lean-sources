import Mathlib

theorem number_theory_146183 : ¬ ∃ x y : ℤ, (x + 7) * (x + 6) = 8 * y + 3 := by
  rintro ⟨x, y, h⟩ 
  have h1 : (x + 7) * (x + 6) % 8 = 3 := by
    omega
  have h2 : (x : ℤ) % 8 = 0 ∨ (x : ℤ) % 8 = 1 ∨ (x : ℤ) % 8 = 2 ∨ (x : ℤ) % 8 = 3 ∨ (x : ℤ) % 8 = 4 ∨ (x : ℤ) % 8 = 5 ∨ (x : ℤ) % 8 = 6 ∨ (x : ℤ) % 8 = 7 := by
    omega
  rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, h2, Int.ofNat] at h1