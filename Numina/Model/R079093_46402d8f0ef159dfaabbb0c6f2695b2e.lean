import Mathlib

theorem number_theory_103893 (a b : ℤ) : ¬(a^4 + 6 ≡ b^3 [ZMOD 13]) := by
  norm_num [Int.ModEq]
  have h1 : a % 13 = 0 ∨ a % 13 = 1 ∨ a % 13 = 2 ∨ a % 13 = 3 ∨ a % 13 = 4 ∨ a % 13 = 5 ∨ a % 13 = 6 ∨ a % 13 = 7 ∨ a % 13 = 8 ∨ a % 13 = 9 ∨ a % 13 = 10 ∨ a % 13 = 11 ∨ a % 13 = 12 := by 
    omega
  have h2 : b % 13 = 0 ∨ b % 13 = 1 ∨ b % 13 = 2 ∨ b % 13 = 3 ∨ b % 13 = 4 ∨ b % 13 = 5 ∨ b % 13 = 6 ∨ b % 13 = 7 ∨ b % 13 = 8 ∨ b % 13 = 9 ∨ b % 13 = 10 ∨ b % 13 = 11 ∨ b % 13 = 12 := by 
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> rcases h2 with (h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h') <;> simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, Int.sub_emod, h, h'] <;> try { omega }
  <;> try { trivial }
  <;> try { tauto }