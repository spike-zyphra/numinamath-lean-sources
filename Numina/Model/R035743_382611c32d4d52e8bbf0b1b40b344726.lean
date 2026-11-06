import Mathlib

theorem number_theory_125467 : ∀ n : ℤ, ¬ 121 ∣ n^2 + 2 * n + 12 := by
  intro n
  intro h
  have h1 : (n ^ 2 + 2 * n + 12) % 121 = 0 := by
    omega
  have h2 : n % 11 = 10 := by
    have h3 : (n ^ 2 + 2 * n + 12) % 11 = 0 := by
      omega
    have h4 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
      omega
    rcases h4 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod] at h3 ⊢ <;> omega
  have h4 : n % 121 = 10 ∨ n % 121 = 21 ∨ n % 121 = 32 ∨ n % 121 = 43 ∨ n % 121 = 54 ∨ n % 121 = 65 ∨ n % 121 = 76 ∨ n % 121 = 87 ∨ n % 121 = 98 ∨ n % 121 = 109 ∨ n % 121 = 120 := by
    omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [h4, pow_two, Int.add_emod, Int.mul_emod] at h1 ⊢
  <;> omega