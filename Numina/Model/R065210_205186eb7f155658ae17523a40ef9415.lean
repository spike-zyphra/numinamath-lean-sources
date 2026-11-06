import Mathlib

theorem number_theory_87865 (x : ℤ) : 120 ∣ 3 * x ^ 5 + 5 * x ^ 3 - 8 * x := by
  have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
    omega
  have h2 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by
    omega
  have h3 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
    omega
  have h4 : (3 * x ^ 5 + 5 * x ^ 3 - 8 * x) % 8 = 0 := by
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1)
    all_goals
      simp [pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h1]
      all_goals omega
  have h5 : (3 * x ^ 5 + 5 * x ^ 3 - 8 * x) % 3 = 0 := by
    rcases h2 with (h2 | h2 | h2)
    all_goals
      simp [pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h2]
      all_goals omega
  have h6 : (3 * x ^ 5 + 5 * x ^ 3 - 8 * x) % 5 = 0 := by
    rcases h3 with (h3 | h3 | h3 | h3 | h3)
    all_goals
      simp [pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h3]
      all_goals omega
  omega