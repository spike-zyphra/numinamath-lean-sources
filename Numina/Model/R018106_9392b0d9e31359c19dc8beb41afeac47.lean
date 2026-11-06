import Mathlib

theorem number_theory_6261 (x : ℤ) (h : 4*x^2+27*x-12 ≡ 0 [ZMOD 15]) : x ≡ -6 [ZMOD 15] ∨ x ≡ 3 [ZMOD 15] := by
  have h1' : (4 * x ^ 2 + 27 * x - 12) % 3 = 0 := by
    have h1 : (4 * x ^ 2 + 27 * x - 12) % 15 = 0 := by
      norm_num [Int.ModEq] at h ⊢
      omega
    omega
  have h2 : x % 3 = 0 := by
    simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, Int.ofNat] at h1' -- simplify the congruence
    have h3 : x % 3 = 0 := by
      have h4 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by 
        omega
      rcases h4 with (h4 | h4 | h4)
      · 
        simp [h4] at h1' ⊢
      · 
        simp [h4] at h1' ⊢
        all_goals 
          omega 
      · 
        simp [h4] at h1' ⊢
        all_goals 
          omega 
    exact h3
  have h3 : (4 * x ^ 2 + 27 * x - 12) % 5 = 0 := by 
    have h1 : (4 * x ^ 2 + 27 * x - 12) % 15 = 0 := by
      norm_num [Int.ModEq] at h ⊢
      omega
    omega
  have h4 : x % 5 = 3 ∨ x % 5 = 4 := by
    have h5 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    rcases h5 with (h5 | h5 | h5 | h5 | h5)
    ·
      simp [h5, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h3 ⊢
    · 
      simp [h5, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h3 ⊢
    ·
      simp [h5, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h3 ⊢
    ·
      simp [h5, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h3 ⊢
      all_goals 
        simp [h5]
    ·
      simp [h5, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h3 ⊢
      all_goals 
        simp [h5]
  have h5 : x % 15 = 3 ∨ x % 15 = 9 := by
    omega
  rcases h5 with (h5 | h5)
  ·
    right
    norm_num [Int.ModEq] at *
    omega
  ·
    left
    norm_num [Int.ModEq] at *
    omega