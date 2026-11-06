import Mathlib
/- How many integers between 1 and 2000 inclusive share no common factors with 2001 ? -/
theorem number_theory_610854 : {a ∈ Finset.range 2001 | Nat.Coprime 2001 a}.card = 1232:= by
  -- Use the totient function to count coprime numbers
  rw [←Nat.totient_eq_card_coprime]
  -- Express 2001 as a product of its prime factors
  rw [show 2001 = 3 * 23 * 29 by norm_num]
  -- Prove that 3 is a prime number
  have g1 : Nat.Prime 3:= by norm_num
  -- Prove that 23 is a prime number
  have g2 : Nat.Prime 23:= by norm_num
  -- Prove that 29 is a prime number
  have g3 : Nat.Prime 29:= by norm_num
  -- Prove that 3 and 23 are coprime
  have g5 : Nat.Coprime 3 23:= by norm_num
  -- Apply the multiplicative property of the totient function for the first multiplication
  rw [Nat.totient_mul]
  -- Apply the multiplicative property of the totient function for the second multiplication
  rw [Nat.totient_mul]
  -- Calculate the totient of prime number 3
  rw [Nat.totient_prime]
  -- Calculate the totient of prime number 23
  rw [Nat.totient_prime]
  -- Calculate the totient of prime number 29
  rw [Nat.totient_prime]
  -- Use all previously proven facts to complete the proof
  all_goals
    assumption
