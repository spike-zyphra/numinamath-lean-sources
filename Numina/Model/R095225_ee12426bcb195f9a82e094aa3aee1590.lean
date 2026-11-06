import Mathlib

theorem number_theory_112624 (n : ℤ) :
    3 ∣ n^3 + (n+1)^3 + (n+2)^3 ∧
    9 ∣ n^3 + (n+1)^3 + (n+2)^3 := by 
  constructor
  · -- Proof of divisibility by 3.
    -- Use direct algebraic approach
    have h1 : n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3 = 3 * (n^3 + 3 * n^2 + 5 * n + 3) := by
      ring_nf
    rw [h1]
    exact ⟨n^3 + 3*n^2 + 5*n + 3, by ring⟩
  · -- Proof of divisibility by 9.
    -- First prove that `n^3 + (n+1)^3 + (n+2)^3` is divisible by 3
    -- then show the quotient is divisible by 3
    have h₁ : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨
      n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
      omega
    rcases h₁ with (h | h | h | h | h | h | h | h | h) <;> ( -- handle each case 
      norm_num [Int.dvd_iff_emod_eq_zero, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, h] -- simplify the expression
      <;> omega 
    ) -- verify the divisibility