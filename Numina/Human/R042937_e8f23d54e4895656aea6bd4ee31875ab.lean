import Mathlib

theorem number_theory_6132 (n : ℤ) :
    n ≡ 0 [ZMOD 2] ∨ n ≡ 0 [ZMOD 3] ∨ n ≡ 1 [ZMOD 4] ∨ n ≡ 5 [ZMOD 6] ∨ n ≡ 7 [ZMOD 12] := by 
  have h : n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 2 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 5 ∨ n % 12 = 6 ∨ n % 12 = 7 ∨ n % 12 = 8 ∨ n % 12 = 9 ∨ n % 12 = 10 ∨ n % 12 = 11 := by 
    omega
  rcases h with (h | h | h | h | h | h | h | h | h | h | h | h)
  all_goals
    simp [Int.ModEq, Int.emod] at *
    omega