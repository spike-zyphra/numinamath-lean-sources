import Mathlib

theorem number_theory_35292 (a : ℤ) (_ : a > 0) :
    ∃ x y : ℤ, x ^ 2 - y ^ 2 = a ^ 3 := by
  use (a ^ 2 + a) / 2, (a ^ 2 - a) / 2
  have h1 : (a ^ 2 + a) % 2 = 0 := by
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by
      omega
    rcases h1 with (h1 | h1)
    · -- If $a$ is even
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.emod_self]
    · -- If $a$ is odd
      simp [h1, pow_two, Int.add_emod, Int.mul_emod, Int.emod_self]
  have h2 : (a ^ 2 - a) % 2 = 0 := by
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by
      omega
    rcases h1 with (h1 | h1)
    · -- If $a$ is even
      simp [h1, pow_two, Int.sub_emod, Int.mul_emod, Int.emod_self]
    · -- If $a$ is odd
      simp [h1, pow_two, Int.sub_emod, Int.mul_emod, Int.emod_self]
  have h3 : ((a ^ 2 + a) / 2 : ℤ) - ((a ^ 2 - a) / 2 : ℤ) = a := by
    omega
  have h4 : ((a ^ 2 + a) / 2 : ℤ) + ((a ^ 2 - a) / 2 : ℤ) = a ^ 2 := by
    omega
  have h5 : ((a ^ 2 + a) / 2 : ℤ) ^ 2 - ((a ^ 2 - a) / 2 : ℤ) ^ 2 = a ^ 3 := by 
    calc 
      ((a ^ 2 + a) / 2 : ℤ) ^ 2 - ((a ^ 2 - a) / 2 : ℤ) ^ 2 
          = (((a ^ 2 + a) / 2 : ℤ) - ((a ^ 2 - a) / 2 : ℤ)) * (((a ^ 2 + a) / 2 : ℤ) + ((a ^ 2 - a) / 2 : ℤ)) := by ring
      _ = a * (a ^ 2) := by 
        rw [h3, h4]
        all_goals nlinarith 
      _ = a ^ 3 := by ring 
  linarith