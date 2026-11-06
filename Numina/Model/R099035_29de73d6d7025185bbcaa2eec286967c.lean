import Mathlib

theorem number_theory_255584 (a : ℤ) : ¬ 15 ∣ (a^2 + a + 2) := by
  intro h
  have h1 : (a ^ 2 + a + 2) % 3 = 0 := by 
    omega
  have h2 : (a % 3) = 0 ∨ (a % 3) = 1 ∨ (a % 3) = 2 := by 
    omega
  rcases h2 with (h2 | h2 | h2)
  · -- a % 3 = 0 
    have h3 : (a ^ 2 + a + 2) % 3 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      all_goals omega
    omega
  · -- a % 3 = 1
    have h3 : (a ^ 2 + a + 2) % 3 = 1 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      all_goals omega
    omega
  · -- a % 3 = 2
    have h3 : (a ^ 2 + a + 2) % 3 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      all_goals omega
    omega