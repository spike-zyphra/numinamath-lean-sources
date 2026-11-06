import Mathlib

theorem number_theory_202730 (n : ℕ) :
    17 ∣ 2^(5*n+3) + 5^n * 3^(n+2) := by
  have h1 : ∀ n : ℕ, 17 ∣ 2^(5 * n + 3) + 5^n * 3^(n + 2) := by 
    intro n 
    induction n with 
    | zero =>
      norm_num
    | succ k ih =>
      have h2 : 2^(5 * (k + 1) + 3) + 5^(k + 1) * 3^(k + 1 + 2) =
        32 * (2^(5 * k + 3)) + 15 * (5 ^k * 3^(k + 2)) := by 
        ring_nf
      rw [h2]
      omega
  exact h1 n