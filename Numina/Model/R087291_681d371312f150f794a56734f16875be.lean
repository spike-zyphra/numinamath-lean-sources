import Mathlib

theorem number_theory_146942 (p : ℤ) (hp : ¬ 2 ∣ p ∧ ¬ 3 ∣ p ∧ ¬ 5 ∣ p) :
    p^4 ≡ 1 [ZMOD 240] := by
  rcases hp with ⟨h1, h2, h3⟩
  have h4 : p % 2 ≠ 0 := by
    intro h
    have : 2 ∣ p := by
      exact Int.dvd_of_emod_eq_zero h
    contradiction
  have h5 : p % 3 ≠ 0 := by
    intro h
    have : 3 ∣ p := by
      exact Int.dvd_of_emod_eq_zero h
    contradiction
  have h6 : p % 5 ≠ 0 := by
    intro h
    have : 5 ∣ p := by
      exact Int.dvd_of_emod_eq_zero h
    contradiction
  have h7 : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by
    omega
  have h8 : p^4 % 16 = 1 := by
    rcases h7 with (h | h | h | h | h | h | h | h)
    · norm_num [pow_succ, Int.mul_emod, h]
    · norm_num [pow_succ, Int.mul_emod, h]
    · norm_num [pow_succ, Int.mul_emod, h]
    · norm_num [pow_succ, Int.mul_emod, h]
    · norm_num [pow_succ, Int.mul_emod, h]
    · norm_num [pow_succ, Int.mul_emod, h]
    · norm_num [pow_succ, Int.mul_emod, h]
    · norm_num [pow_succ, Int.mul_emod, h]
  have h9 : p^4 % 3 = 1 := by
    have h9 : p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h9 with (h | h)
    · norm_num [pow_succ, h, Int.mul_emod]
    · norm_num [pow_succ, h, Int.mul_emod]
  have h10 : p^4 % 5 = 1 := by
    have h10 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
      omega
    rcases h10 with (h | h | h | h)
    · norm_num [pow_succ, h, Int.mul_emod]
    · norm_num [pow_succ, h, Int.mul_emod]
    · norm_num [pow_succ, h, Int.mul_emod]
    · norm_num [pow_succ, h, Int.mul_emod]
  norm_num [Int.ModEq]
  omega