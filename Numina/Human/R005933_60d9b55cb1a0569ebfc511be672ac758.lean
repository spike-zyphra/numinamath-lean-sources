import Mathlib

--theorem: Compute the largest prime factor of $3^{12}+3^{9}+3^{5}+1$.

theorem largest_prime_factor_of_expression : 41 = (Nat.primeFactorsList (3^12 + 3^9 + 3^5 + 1)).maximum := by
  -- First, verify that our target number is indeed equal to 551368.
  let expression := 3^12 + 3^9 + 3^5 + 1
  have h_value : expression = 551368 := by
    norm_num

  -- Confirm that the maximum element in the list of prime factors of this value is 41.
  have h_factors : Nat.primeFactorsList expression = [2, 2, 2, 41, 41, 41] := by
    native_decide
  
  have h_largest_prime : 41 = List.maximum (Nat.primeFactorsList expression) := by
    rw [h_factors]
    simp [List.maximum]
    simp_all
    decide

  -- Conclude with the fact that the maximum of the list of prime factors is 41.
  rw [h_largest_prime]
