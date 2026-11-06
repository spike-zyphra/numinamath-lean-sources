import Mathlib

theorem number_theory_128950 (a : ℕ) : a^5 ≡ 0 [ZMOD 11] ∨ a^5 ≡ 1 [ZMOD 11] ∨ a^5 ≡ -1 [ZMOD 11] := by 
  have h1 : (a : ℤ) % 11 = 0 ∨ (a : ℤ) % 11 = 1 ∨ (a : ℤ) % 11 = 2 ∨ (a : ℤ) % 11 = 3 ∨ (a : ℤ) % 11 = 4 ∨ (a : ℤ) % 11 = 5 ∨ (a : ℤ) % 11 = 6 ∨ (a : ℤ) % 11 = 7 ∨ (a : ℤ) % 11 = 8 ∨ (a : ℤ) % 11 = 9 ∨ (a : ℤ) % 11 = 10 := by 
    omega

  rcases h1 with (h | h | h | h | h | h | h | h | h | h | h)
  · -- Case where a ≡ 0 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 1 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 2 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 3 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 4 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 5 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 6 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 7 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 8 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 9 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]
  · -- Case where a ≡ 10 [ZMOD 11]
    norm_num [Int.ModEq, pow_succ, Int.mul_emod, h]