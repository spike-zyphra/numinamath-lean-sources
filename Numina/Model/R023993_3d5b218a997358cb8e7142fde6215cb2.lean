import Mathlib.Tactic

theorem number_theory_128787 : ¬ ∃ m n : ℤ, m ^ 2 + 3 * m * n - 2 * n ^ 2 = 122 := by 
  rintro ⟨m, n, h⟩
  have eq1 : (2 * m + 3 * n) ^ 2 - 17 * n ^ 2 = 488 := by
    nlinarith
  have h1 : (2 * m + 3 * n) ^ 2 % 17 = 12 % 17 := by 
    omega
  have h2 : (2 * m + 3 * n) % 17 = 0 ∨ (2 * m + 3 * n) % 17 = 1 ∨ (2 * m + 3 * n) % 17 = 2 ∨ (2 * m + 3 * n) % 17 = 3 ∨ (2 * m + 3 * n) % 17 = 4 ∨ (2 * m + 3 * n) % 17 = 5 ∨ (2 * m + 3 * n) % 17 = 6 ∨ (2 * m + 3 * n) % 17 = 7 ∨ (2 * m + 3 * n) % 17 = 8 ∨ (2 * m + 3 * n) % 17 = 9 ∨ (2 * m + 3 * n) % 17 = 10 ∨ (2 * m + 3 * n) % 17 = 11 ∨ (2 * m + 3 * n) % 17 = 12 ∨ (2 * m + 3 * n) % 17 = 13 ∨ (2 * m + 3 * n) % 17 = 14 ∨ (2 * m + 3 * n) % 17 = 15 ∨ (2 * m + 3 * n) % 17 = 16 := by 
    omega
  rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h2] at h1
  all_goals omega