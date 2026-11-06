import Mathlib

theorem number_theory_7680 (m n : ℕ) : ¬(0 < m ∧ 0 < n ∧ m^3 + n^4 = 19^19) := by
  by_contra h
  rcases h with ⟨hm, hn, heq⟩
  have h1 : m ^ 3 % 13 = 0 ∨ m ^ 3 % 13 = 1 ∨ m ^ 3 % 13 = 5 ∨ m ^ 3 % 13 = 8 ∨ m ^ 3 % 13 = 12 := by
    have h11 : m % 13 = 0 ∨ m % 13 = 1 ∨ m % 13 = 2 ∨ m % 13 = 3 ∨ m % 13 = 4 ∨ m % 13 = 5 ∨ m % 13 = 6 ∨ m % 13 = 7 ∨ m % 13 = 8 ∨ m % 13 = 9 ∨ m % 13 = 10 ∨ m % 13 = 11 ∨ m % 13 = 12 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h | h | h)
    <;> norm_num [h, Nat.pow_mod] at *
  have h2 : n ^ 4 % 13 = 0 ∨ n ^ 4 % 13 = 1 ∨ n ^ 4 % 13 = 3 ∨ n ^ 4 % 13 = 9 := by
    have h21 : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by
      omega
    rcases h21 with (h | h | h | h | h | h | h | h | h | h | h | h | h)
    <;> norm_num [h, Nat.pow_mod] at *
  have eq1 : (19 ^ 19 : ℕ) % 13 = 7 := by
    norm_num
  have eq2 : (m ^ 3 + n ^ 4) % 13 = 7 := by
    omega
  omega