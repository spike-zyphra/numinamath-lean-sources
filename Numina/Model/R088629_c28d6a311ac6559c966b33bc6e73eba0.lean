import Mathlib

theorem number_theory_275656 (n : ℤ) (h : ¬ 5 ∣ n) :
    5 ∣ n^2 + 1 ∨ 5 ∣ n^2 - 1 := by
  have h1 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega

  rcases h1 with (h | h | h | h)
  · -- case n % 5 = 1
    have h2 : (n ^ 2 - 1) % 5 = 0 := by
      simp [pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, h]
      all_goals omega
    right
    omega
  · -- case n % 5 = 2
    have h2 : (n ^ 2 + 1) % 5 = 0 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
      all_goals omega
    left
    omega
  · -- case n % 5 = 3
    have h2 : (n ^ 2 + 1) % 5 = 0 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
      all_goals omega
    left
    omega
  · -- case n % 5 = 4
    have h2 : (n ^ 2 - 1) % 5 = 0 := by
      simp [pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, h]
      all_goals omega
    right
    omega