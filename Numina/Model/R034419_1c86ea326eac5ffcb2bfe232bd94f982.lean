import Mathlib

theorem number_theory_217259 (n : ℕ) :
    11 ∣ 3^(2*n + 2) + 2^(6*n + 1) := by 
  have h1 : ∀ (n : ℕ), 11 ∣ 3 ^ (2 * n + 2) + 2 ^ (6 * n + 1) := by
    intro n 
    induction n with 
    | zero => 
      norm_num
    | succ k ih =>
      have h2 : 3 ^ (2 * (k + 1) + 2) + 2 ^ (6 * (k + 1) + 1) = 
          9 * (3 ^ (2 * k + 2)) + 64 * (2 ^ (6 * k + 1)) := by 
        ring_nf
      rw [h2] 
      omega
  specialize h1 n
  simpa using h1