import Mathlib

theorem number_theory_14449 : Set.encard {n : ℕ | 2 ≤ n ∧ (Nat.ofDigits n [1, 0, 0, 1]).Prime} = 0 := by 
  have h1 : {n : ℕ | 2 ≤ n ∧ (Nat.ofDigits n [1, 0, 0, 1]).Prime} = ∅ := by 
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false] 
    intro h
    rcases h with ⟨h2, h3⟩
    -- First, let's compute what Nat.ofDigits n [1, 0, 0, 1] means.
    -- This is the base-n expansion of the digits [1,0,0,1], which is 1*x^3 + 0*x^2 + 0*x + 1 = x^3 +1.
    -- So we compute first the value of this in base n.
    have h4 : Nat.ofDigits n [1, 0, 0, 1] = n ^ 3 + 1 := by
      simp [Nat.ofDigits, mul_add, add_mul, pow_succ, pow_zero, mul_zero, add_zero, zero_add]
      <;> ring 
    -- Now rewrite the primality condition using the explicit formula.
    rw [h4] at h3 
    -- Now, we need to show that n^3 +1 is not prime.
    -- Note that n^3 +1 = (n+1)(n^2-n+1).
    -- Let's prove this equality.
    have h5 : ¬ (n ^ 3 + 1).Prime := by
      have h6 : n ^ 3 + 1 = (n + 1) * (n ^ 2 - n + 1) := by 
        cases n with
        | zero => linarith -- contradicts n ≥ 2 
        | succ n => 
          cases n with
          | zero => linarith -- contradicts n ≥ 2 (n would be 1)
          | succ n => -- n = n+2, so n ≥ 2.
            simp [pow_three, Nat.mul_sub, Nat.add_mul, Nat.mul_add, mul_add, add_mul, pow_two] at *
            <;> ring_nf at *
            <;> omega 
      -- Now that we have expressed n^3 +1 as a product of two factors, we show these factors are greater than 1.
      rw [h6] at h3
      have h7 : n ≥ 2 := by linarith 
      have h8 : n + 1 > 1 := by omega 
      have h9 : n ^ 2 - n + 1 > 1 := by
        have h7 : n ≥ 2 := by linarith 
        have h8 : n ^ 2 ≥ 2 * n := by nlinarith 
        have h9 : n ^ 2 ≥ n + 2 := by nlinarith 
        omega 
      -- Now we can apply that a number = a*b, with a > 1 and b > 1 is not prime.
      apply Nat.not_prime_mul (by omega) (by omega) at h3
      contradiction 
    contradiction 
  rw [h1] 
  simp