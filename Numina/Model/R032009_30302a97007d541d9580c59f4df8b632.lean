import Mathlib

theorem number_theory_234852 (n : ℕ) :
    33 ∣ (7 : ℤ)^(2*n) - 4^(2*n) ∧ 35 ∣ (3 : ℤ)^(6*n) - 2^(6*n) := by
  constructor
  · -- Prove that $7^{2n} - 4^{2n}$ is divisible by 33
    have h1 : ∀ n : ℕ, 33 ∣ (7 : ℤ) ^ (2 * n) - 4 ^ (2 * n) := by
      intro n 
      induction n with 
      | zero =>
        norm_num
      | succ k ih =>
        have eq1 : (7 : ℤ) ^ (2 * (k + 1)) - 4 ^ (2 * (k + 1)) =
            49 * ((7 : ℤ) ^ (2 * k)) - 16 * ((4 : ℤ) ^ (2 * k)) := by 
          ring_nf
        rw [eq1]
        omega 
    exact h1 n
  · -- Prove that $3^{6n} - 2^{6n}$ is divisible by 35
    have h2 : ∀ n : ℕ, 35 ∣ (3 : ℤ) ^ (6 * n) - 2 ^ (6 * n) := by 
      intro n 
      induction n with 
      | zero =>
        norm_num 
      | succ k ih =>
        have eq2 : (3 : ℤ) ^ (6 * (k + 1)) - 2 ^ (6 * (k + 1)) =
            (3 ^ 6) * ((3 : ℤ) ^ (6 * k)) - (2 ^ 6) * ((2 : ℤ) ^ (6 * k)) := by 
          ring_nf
        rw [eq2]
        omega
    exact h2 n