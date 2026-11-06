import Mathlib


lemma lemma_1 (a : ℤ) (ha : Odd a) : a^4 ≡ 1 [ZMOD 16] := by
  have h1 : a % 16 = 1 ∨ a % 16 = 3 ∨ a % 16 = 5 ∨ a % 16 = 7 ∨ a % 16 = 9 ∨ a % 16 = 11 ∨ a % 16 = 13 ∨ a % 16 = 15 := by
    rcases ha with ⟨k, hk⟩
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1)
  all_goals
    simp [Int.ModEq, pow_succ, Int.add_emod, Int.mul_emod, h1]
    all_goals omega


theorem number_theory_275675 (a : ℤ) (h : Odd a) : 16 ∣ a^4 + 9 * (9 - 2 * a^2) := by
  have h3 : a % 16 = 1 ∨ a % 16 = 3 ∨ a % 16 = 5 ∨ a % 16 = 7 ∨ a % 16 = 9 ∨ a % 16 = 11 ∨ a % 16 = 13 ∨ a % 16 = 15 := by 
    rcases h with ⟨k, hk⟩
    omega
  rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3)
  all_goals 
    simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.mul_emod, pow_two, pow_succ, Int.sub_emod, h3]
    all_goals omega