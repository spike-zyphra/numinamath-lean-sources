import Mathlib

theorem number_theory_208199 (n : ℕ) :
  7 ∣ 2^(n + 2) + 3^(2 * n + 1) := by
  have h1 : ∀ (n : ℕ), 7 ∣ 2 ^ (n + 2) + 3 ^ (2 * n + 1) := by
    intro n 
    induction n with 
    | zero =>
      norm_num
    | succ k ih =>
      have h2 : (2 ^ (k + 3) + 3 ^ (2 * (k + 1) + 1)) % 7 = 0 := by
        have h2 : (2 ^ (k + 2) + 3 ^ (2 * k + 1)) % 7 = 0 := by
          omega
        have h5 : (2 ^ (k + 3) + 3 ^ (2 * (k + 1) + 1)) % 7 = (2 * (2 ^ (k + 2) ) + 9 * (3 ^ (2 * k + 1)) ) % 7 := by
          ring_nf
        rw [h5] 
        omega
      have h3 : 7 ∣ (2 ^ (k + 3) + 3 ^ (2 * (k + 1) + 1)) := by 
        omega
      have h4 : (2 ^ (k + 1 + 2) + 3 ^ (2 * (k + 1) + 1) ) = (2 ^ (k + 3) + 3 ^ (2 * (k + 1) + 1) ) := by 
        ring_nf
      rw [h4] 
      exact h3
  specialize h1 n 
  simpa using h1