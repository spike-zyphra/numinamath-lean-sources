import Mathlib
/- How many digits are in the base two representation of 10 ! (factorial)? -/
theorem number_theory_610950 : (Nat.digits 2 (Nat.factorial 10)).length = 22:= by
  -- Use the digits_len lemma to relate the length of digits to the logarithm
  rw [Nat.digits_len]
  .
    -- Calculate the exact value of 10!
    have h : Nat.factorial 10 = 3628800:= by simp [Nat.factorial_succ]
    -- Substitute this value
    rw [h]
    -- Simplify expressions
    simp
    -- Apply a lemma about logarithms and powers
    apply Nat.log_eq_of_pow_le_of_lt_pow
    .
      -- Prove the lower bound
      simp
    .
      -- Prove the upper bound
      simp
  .
    -- Simplify remaining expressions
    simp
  .
    -- Prove that 10! is not zero (required for logarithm to be defined)
    exact Nat.factorial_ne_zero 10
