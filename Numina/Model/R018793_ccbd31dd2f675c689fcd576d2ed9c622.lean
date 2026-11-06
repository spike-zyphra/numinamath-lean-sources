import Mathlib

theorem number_theory_124304 (n : ℤ) : n^13 - n ≡ 0 [ZMOD 2730] := by
  have h1 : n ^ 13 % 2 = n % 2 := by 
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases h2 with (h2 | h2)
    · 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod]

  have h2 : n ^ 13 % 3 = n % 3 := by
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h3 with (h3 | h3 | h3)
    · 
      simp [h3, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h3, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h3, pow_succ, Int.add_emod, Int.mul_emod]

  have h3 : n ^ 13 % 5 = n % 5 := by 
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega 
    rcases h4 with (h4 | h4 | h4 | h4 | h4)
    · 
      simp [h4, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h4, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h4, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h4, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h4, pow_succ, Int.add_emod, Int.mul_emod]

  have h4 : n ^ 13 % 7 = n % 7 := by
    have h5 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by 
      omega 
    rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5)
    · 
      simp [h5, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h5, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h5, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h5, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h5, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h5, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h5, pow_succ, Int.add_emod, Int.mul_emod]

  have h5 : n ^ 13 % 13 = n % 13 := by
    have h6 : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by
      omega 
    rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6)
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    · 
      simp [h6, pow_succ, Int.add_emod, Int.mul_emod]

  norm_num [Int.ModEq]
  omega