import Mathlib

theorem algebra_112504 (n : ℤ) : 120 ∣ n^5 - 5 * n^3 + 4 * n := by
  -- we need to prove the given expression is divisible by 120 
  -- we let the expression be p
  -- We need to prove p % 120 = 0
  -- which is equivalent to proving p % 8 = 0, p % 3 = 0, p % 5 = 0
  -- Now we compute each one
  -- compute p modulo 8
  have h1 : (n ^ 5 - 5 * n ^ 3 + 4 * n) % 8 = 0 := by
    have h2 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h) <;> simp [h, Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ] at *
  
  -- compute p modulo 3
  have h2 : (n ^ 5 - 5 * n ^ 3 + 4 * n) % 3 = 0 := by
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h3 with (h | h | h) <;> simp [h, Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ] at *
  
  -- compute p modulo 5
  have h3 : (n ^ 5 - 5 * n ^ 3 + 4 * n) % 5 = 0 := by
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h4 with (h | h | h | h | h) <;> simp [h, Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ] at *
  
  omega
  all_goals tauto