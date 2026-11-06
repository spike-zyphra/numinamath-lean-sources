import Mathlib

theorem number_theory_106233 (n : ℕ) (hn : 2 ≤ n) :
    ¬Nat.Prime (n^4 + n^2 + 1) := by

  have h1 : n ^ 4 + n ^ 2 + 1 = (n^2 + n + 1) * (n^2 - n + 1) := by
    cases n with
    | zero =>
      linarith -- contradicts with the hypothesis 2 <= n
    | succ n =>
      cases n with
      | zero =>
        linarith -- contradicts with the hypothesis 2 <= n
      | succ n =>
        simp [pow_succ, pow_zero, Nat.mul_add, Nat.add_mul]
        <;> ring_nf <;> omega

  have h3 : (n ^ 2 + n + 1) > 1 := by
    have h3 : n ≥ 2 := by 
      linarith
    nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((n : ℕ) + 1)]

  have h4 : (n ^ 2 - n + 1) > 1 := by
    have h6 : n ≥ 2 := by 
      linarith
    have h7 : n ^ 2 ≥ n := by nlinarith
    have h8 : n ^ 2 - n ≥ 1 := by
      have h9 : n ^ 2 ≥ n + 1 := by
        nlinarith [sq_nonneg ((n : ℕ) - 2 : ℤ), sq_nonneg ((n : ℕ) : ℤ)]
      omega
    omega

  rw [h1]
  apply Nat.not_prime_mul (by omega) (by omega)