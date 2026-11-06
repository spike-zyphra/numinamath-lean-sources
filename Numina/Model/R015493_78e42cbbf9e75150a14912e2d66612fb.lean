import Mathlib

theorem number_theory_6454 (x : ℤ) :
    21*x^18+2*x^15-x^10+4*x-3 ≡ 0 [ZMOD 7] ↔ x^4-2*x^3-4*x+3 ≡ 0 [ZMOD 7] := by
  have h1 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [Int.ModEq, 
      pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h1, Int.mul_emod, Int.add_emod, 
      Int.sub_emod] <;> omega