import Mathlib

theorem number_theory_161523 : ∃ n : ℕ, n > 0 ∧ ∃ m : ℕ, m > 0 ∧ 3^n = 10^4 * m + 1 := by
  use 500
  constructor
  · -- Show that n > 0
    norm_num
  · -- We need to provide m such that m > 0 and 3^500 = 10^4 * m + 1
    use (3 ^ 500 - 1) / (10 ^ 4)
    constructor
    · -- Show that m > 0
      have h1 : 3 ^ 500 > 1 := by
        have h2 : 3 ^ 1 > 1 := by norm_num
        have h3 : 3 ^ 500 > 3 ^ 1 := by
          apply Nat.pow_lt_pow_of_lt
          all_goals linarith
        have h4 : 3 ^ 500 > 1 := by linarith [h3, h2]
        linarith
      have h2 : (3 ^ 500 - 1) / (10 ^ 4) > 0 := by
        apply Nat.div_pos
        · -- Show 3^500 - 1 > 10^4
          omega
        all_goals omega
      linarith [h2]
    · -- Show that 3 ^ 500 = 10 ^ 4 * m + 1
      have h3 : 3 ^ 500 % (10 ^ 4) = 1 := by
        norm_num
      have h4 : 3 ^ 500 = 10 ^ 4 * ((3 ^ 500 - 1) / (10 ^ 4)) + 1 := by
        omega
      linarith [h4]