import Mathlib

theorem number_theory_244548 (n : ℕ) :
    17 ∣ 6^(2*n) + 2^(n + 2) + 12 * 2^n := by
  have h1 : ∀ (n : ℕ), 17 ∣ 6^(2*n) + 2^(n + 2) + 12 * 2^n := by 
    intro n
    induction n with 
    | zero =>
      norm_num
    | succ k ih =>
      have h2 : 6 ^ (2 * (k + 1)) + 2 ^ ((k + 1) + 2) + 12 * 2 ^ (k + 1) =
          36 * (6 ^ (2 * k)) + 2 * (2 ^ (k + 2)) + 24 * (2 ^ k) := by 
        ring_nf
      rw [h2]
      omega
  specialize h1 n
  simpa using h1