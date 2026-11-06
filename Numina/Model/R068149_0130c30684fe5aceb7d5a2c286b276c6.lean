import Mathlib

theorem number_theory_188731 : ¬∃ n : ℤ, 5 ∣ n^2 - 8 := by
  rintro ⟨n, hn⟩
  have h1 : n^2 % 5 = 0 ∨ n^2 % 5 = 1 ∨ n^2 % 5 = 4 := by
    have h1 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1)
    · -- case n ≡ 0
      simp [pow_two, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      all_goals omega
    · -- case n ≡ 1
      simp [pow_two, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      all_goals omega
    · -- case n ≡ 2
      simp [pow_two, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      all_goals omega
    · -- case n ≡ 3
      simp [pow_two, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      all_goals omega
    · -- case n ≡ 4
      simp [pow_two, Int.mul_emod, h1, Int.add_emod, Int.sub_emod]
      all_goals omega
  have h2 : n^2 % 5 = 3 := by
    omega
  omega