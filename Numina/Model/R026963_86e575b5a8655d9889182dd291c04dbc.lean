import Mathlib

theorem number_theory_255249 (n : ℤ) : ¬ ∃ m, m^2 = n^2 + (n+1)^2 + (n+2)^2 + (n+3)^2 + (n+4)^2 := by
  rintro ⟨m, hm⟩
  have eq1 : m ^ 2 = 5 * n ^ 2 + 20 * n + 30 := by
    nlinarith
  have eq2 : m ^ 2 = 5 * (n + 2) ^ 2 + 10 := by
    nlinarith [eq1]
  have eq3 : m ^ 2 % 5 = 0 ∨ m ^ 2 % 5 = 1 ∨ m ^ 2 % 5 = 4 := by
    have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1)
    · -- m ≡ 0
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      <;> omega
    · -- m ≡ 1
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      <;> omega
    · -- m ≡ 2
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      <;> omega
    · -- m ≡ 3
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      <;> omega
    · -- m ≡ 4
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      <;> omega
  have eq4 : m ^ 2 % 5 = 0 := by
    omega
  have eq5 : m % 5 = 0 := by 
    have h1 : m ^ 2 % 5 = 0 := eq4
    have h2 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2)
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, h2] at h1 ⊢ 
      <;> omega
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, h2] at h1 ⊢
      all_goals omega
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, h2] at h1 ⊢
      all_goals omega
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, h2] at h1 ⊢
      all_goals omega
    · 
      simp [Int.add_emod, Int.mul_emod, pow_two, h2] at h1 ⊢
      all_goals omega
  have eq6 : ∃ t, m = 5 * t := by 
    refine' ⟨m / 5, by omega⟩
  rcases eq6 with ⟨t, ht⟩
  rw [ht] at eq1
  have eq7 : 5 * t ^ 2 = (n + 2) ^ 2 + 2 := by
    nlinarith
  have eq8 : (n + 2) ^ 2 % 5 = 0 ∨ (n + 2) ^ 2 % 5 = 1 ∨ (n + 2) ^ 2 % 5 = 4 := by 
    have h1 : (n + 2) % 5 = 0 ∨ (n + 2) % 5 = 1 ∨ (n + 2) % 5 = 2 ∨ (n + 2) % 5 = 3 ∨ (n + 2) % 5 = 4 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1)
    · 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      all_goals omega
    · 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      all_goals omega
    · 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      all_goals omega
    · 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      all_goals omega
    · 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      all_goals omega
  have eq9 : (n + 2) ^ 2 % 5 = 3 := by
    omega
  omega