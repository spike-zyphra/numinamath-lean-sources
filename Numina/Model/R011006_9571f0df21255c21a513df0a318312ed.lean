import Mathlib

  theorem number_theory_3192 : ¬ ∃ n : ℤ, n^2 ≡ 3 [ZMOD 4] := by
  rintro ⟨n, hn⟩
  have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    omega
  rcases h1 with (h | h | h | h)
  · -- n ≡ 0 [ZMOD 4]
    have h2 : n ^ 2 % 4 = 0 := by
      simp [pow_two, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
    norm_num [Int.ModEq] at hn
    omega
  · -- n ≡ 1 [ZMOD 4]
    have h2 : n ^ 2 % 4 = 1 := by
      simp [pow_two, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
    norm_num [Int.ModEq] at hn
    omega
  · -- n ≡ 2 [ZMOD 4]
    have h2 : n ^ 2 % 4 = 0 := by
      simp [pow_two, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
    norm_num [Int.ModEq] at hn
    omega
  · -- n ≡ 3 [ZMOD 4]
    have h2 : n ^ 2 % 4 = 1 := by
      simp [pow_two, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
    norm_num [Int.ModEq] at hn
    omega