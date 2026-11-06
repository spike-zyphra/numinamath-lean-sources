import Mathlib

theorem number_theory_36509 (n : ℤ) : 6 ∣ 2 * n ^ 3 + 3 * n ^ 2 + 7 * n := by
  have h1 : (2 * n ^ 3 + 3 * n ^ 2 + 7 * n) % 2 = 0 := by
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases h2 with (h2 | h2)
    ·
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2]
      <;> omega
    ·
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h2]
      <;> omega
  have h2 : (2 * n ^ 3 + 3 * n ^ 2 + 7 * n) % 3 = 0 := by
    have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h1 with (h1 | h1 | h1)
    ·
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h1]
      <;> omega
    ·
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h1]
      <;> omega
    ·
      simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h1]
      <;> omega
  omega