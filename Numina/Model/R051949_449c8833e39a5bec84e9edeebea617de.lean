import Mathlib

theorem number_theory_144267 (n : ℤ) :
    n^2 ≡ 0 [ZMOD 4] ∨ n^2 ≡ 1 [ZMOD 4] := by 
  have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
    omega
  rcases h1 with (h | h | h | h)
  · -- Case 1: n % 4 = 0
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    <;> tauto
  · -- Case 2: n % 4 = 1
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    <;> tauto
  · -- Case 3: n % 4 = 2
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    <;> tauto
  · -- Case 4: n % 4 = 3
    simp [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    <;> tauto