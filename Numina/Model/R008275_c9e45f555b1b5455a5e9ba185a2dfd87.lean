import Mathlib

theorem number_theory_4663 (n : ℤ) :
    n^4 ≡ 0 [ZMOD 10] ∨
    n^4 ≡ 1 [ZMOD 10] ∨
    n^4 ≡ 5 [ZMOD 10] ∨
    n^4 ≡ 6 [ZMOD 10] := by 
  have h : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨
    n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
    omega
  rcases h with (h | h | h | h | h | h | h | h | h | h) <;> simp [Int.ModEq, pow_succ, Int.add_emod, Int.mul_emod, h, Int.emod] <;> omega