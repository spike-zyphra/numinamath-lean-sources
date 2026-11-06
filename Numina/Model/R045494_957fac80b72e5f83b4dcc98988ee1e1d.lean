import Mathlib

theorem number_theory_47025 (n : ℤ) : ¬n^2 ≡ 2 [ZMOD 3] := by 
  intro h
  have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
    omega
  rcases h1 with (h1 | h1 | h1)
  · -- case where n ≡ 0 [mod 3]
    have h2 : n ^ 2 % 3 = 0 := by
      simp [pow_two, Int.mul_emod, h1]
    norm_num [Int.ModEq] at h
    omega
  · -- case where n ≡ 1 [mod 3]
    have h2 : n ^ 2 % 3 = 1 := by 
      simp [pow_two, Int.mul_emod, h1, Int.add_emod]
    norm_num [Int.ModEq] at h
    omega
  · -- case where n ≡ 2 [mod 3]
    have h2 : n ^ 2 % 3 = 1 := by 
      simp [pow_two, Int.mul_emod, h1, Int.add_emod]
    norm_num [Int.ModEq] at h 
    omega