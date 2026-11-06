import Mathlib

theorem number_theory_166085 (n : ℤ) :
    n^20 ≡ 0 [ZMOD 100] ∨
    n^20 ≡ 1 [ZMOD 100] ∨
    n^20 ≡ 25 [ZMOD 100] ∨
    n^20 ≡ 76 [ZMOD 100] := by

  have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    omega

  have h2 : n % 25 = 0 ∨ n % 25 = 1 ∨ n % 25 = 2 ∨ n % 25 = 3 ∨ n % 25 = 4 ∨
      n % 25 = 5 ∨ n % 25 = 6 ∨ n % 25 = 7 ∨ n % 25 = 8 ∨ n % 25 = 9 ∨
      n % 25 = 10 ∨ n % 25 = 11 ∨ n % 25 = 12 ∨ n % 25 = 13 ∨ n % 25 = 14 ∨
      n % 25 = 15 ∨ n % 25 = 16 ∨ n % 25 = 17 ∨ n % 25 = 18 ∨ n % 25 = 19 ∨
      n % 25 = 20 ∨ n % 25 = 21 ∨ n % 25 = 22 ∨ n % 25 = 23 ∨ n % 25 = 24 := by
    omega
  
  have h4 : n ^ 20 % 4 = 0 ∨ n ^ 20 % 4 = 1 := by
    rcases h1 with (h | h | h | h) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, h, Int.emod, Int.add_emod, Int.mul_emod, Int.sub_emod] <;> omega

  have h25 : n ^ 20 % 25 = 0 ∨ n ^ 20 % 25 = 1 := by
    rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, h, Int.emod, Int.add_emod, Int.mul_emod, Int.sub_emod] <;> omega

  have h3 : n ^ 20 % 100 = 0 ∨ n ^ 20 % 100 = 1 ∨ n ^ 20 % 100 = 25 ∨ n ^ 20 % 100 = 76 := by
    omega

  rcases h3 with (h | h | h | h)
  · -- n^20 ≡ 0 [ZMOD 100]
    simp [Int.ModEq, h]
  · -- n^20 ≡ 1 [ZMOD 100]
    simp [Int.ModEq, h]
  · -- n^20 ≡ 25 [ZMOD 100]
    simp [Int.ModEq, h]
  · -- n^20 ≡ 76 [ZMOD 100]
    simp [Int.ModEq, h]