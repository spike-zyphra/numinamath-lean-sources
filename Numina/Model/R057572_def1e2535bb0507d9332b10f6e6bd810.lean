import Mathlib

theorem number_theory_159965 (n : ℤ) (h₀ : Odd n) : n^2 ≡ 1 [ZMOD 8] := by
  have h1 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    rcases h₀ with ⟨k, hk⟩
    omega
  rcases h1 with (h | h | h | h)
  · 
    norm_num [Int.ModEq, pow_two, Int.mul_emod, Int.add_emod, h]
  · 
    norm_num [Int.ModEq, pow_two, Int.mul_emod, Int.add_emod, h]
  · 
    norm_num [Int.ModEq, pow_two, Int.mul_emod, Int.add_emod, h]
  · 
    norm_num [Int.ModEq, pow_two, Int.mul_emod, Int.add_emod, h]