import Mathlib

theorem number_theory_116737 (n : ℕ) :
    7 ∣ 3^(12*n + 1) + 2^(6*n + 2) := by 
  have h1 : ∀ (n : ℕ), 7 ∣ 3 ^ (12 * n + 1) + 2 ^ (6 * n + 2) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      norm_num [pow_add, pow_mul] at ih ⊢
      ring_nf at ih ⊢
      omega
  exact h1 n