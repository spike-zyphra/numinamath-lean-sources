import Mathlib

theorem number_theory_106348 (n : ℤ) :
    n^2 ≡ 0 [ZMOD 4] ∨ n^2 ≡ 1 [ZMOD 4] := by
  have h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    omega
  rcases h with (h | h | h | h)
  · -- Case n % 4 = 0
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h]
  · -- Case n % 4 = 1
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h]
  · -- Case n % 4 = 2
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h]
  · -- Case n % 4 = 3
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h]