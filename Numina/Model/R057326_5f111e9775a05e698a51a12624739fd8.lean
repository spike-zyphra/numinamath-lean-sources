import Mathlib

theorem number_theory_244262 (n : ℕ) :
    11 ∣ 5^(2*n) + 3^(n + 2) + 3^n := by
  have h1 : ∀ n : ℕ, 11 ∣ 5 ^ (2 * n) + 3 ^ (n + 2) + 3 ^ n := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have eq1 : 5 ^ (2 * (n + 1)) + 3 ^ ((n + 1) + 2) + 3 ^ (n + 1) =
          25 * 5 ^ (2 * n) + 3 * 3 ^ (n + 2) + 3 * 3 ^ n := by
        ring_nf
      rw [eq1]
      omega
  specialize h1 n
  simpa using h1