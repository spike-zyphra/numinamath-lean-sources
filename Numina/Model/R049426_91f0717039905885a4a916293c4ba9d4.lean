import Mathlib

theorem number_theory_147137 (n : ℕ) :
    n^2 ≡ 0 [ZMOD 8] ∨ n^2 ≡ 1 [ZMOD 8] ∨ n^2 ≡ 4 [ZMOD 8] := by
  have h1 : (n : ℤ) % 8 = 0 ∨ (n : ℤ) % 8 = 1 ∨ (n : ℤ) % 8 = 2 ∨ (n : ℤ) % 8 = 3 ∨ (n : ℤ) % 8 = 4 ∨ (n : ℤ) % 8 = 5 ∨ (n : ℤ) % 8 = 6 ∨ (n : ℤ) % 8 = 7 := by
    omega
  rcases h1 with (h | h | h | h | h | h | h | h) <;> norm_num [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h]