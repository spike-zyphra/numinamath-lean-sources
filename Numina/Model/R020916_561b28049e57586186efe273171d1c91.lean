import Mathlib

theorem number_theory_69577 (n : ℤ) (hn : n > 1) : 12 ∣ n^4 - n^2 := by
  have h1 : n ^ 4 % 3 = n ^ 2 % 3 := by
    have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    ·
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h2, Int.sub_emod]
    ·
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h2, Int.sub_emod]
    ·
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h2, Int.sub_emod]
  have h2 : n ^ 4 % 4 = n ^ 2 % 4 := by
    have h3 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3)
    ·
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h3, Int.sub_emod]
      all_goals omega
    ·
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h3, Int.sub_emod]
      all_goals omega
    ·
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h3, Int.sub_emod]
      all_goals omega
    ·
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h3, Int.sub_emod]
      all_goals omega
  omega