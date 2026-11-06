import Mathlib

theorem number_theory_598193 (n : ℕ) :
    1989 ∣ 13 * (-50 : ℤ) ^ n + 17 * 40 ^ n - 30 := by
  have h1 : ∀ n : ℕ, 1989 ∣ 13 * (-50 : ℤ) ^ n + 17 * 40 ^ n - 30 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      norm_num [pow_succ, pow_zero] at ih ⊢
      omega
  specialize h1 n
  simpa using h1