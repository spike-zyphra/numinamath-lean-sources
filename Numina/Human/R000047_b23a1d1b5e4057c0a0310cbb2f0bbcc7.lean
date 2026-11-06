import Mathlib
/-- What is the result if you add the largest odd two-digit number to the smallest even three-digit number？ -/
theorem Arithmetic_4181 :
  (99 : ℕ) + 100 = 199 := by
  -- 1. Indentify the largest two-digit odd number 
  have h1 : ∀ n : ℕ, n < 100 → n ≤ 99 := by
    intro n hn
    exact Nat.le_of_lt_succ hn

  have h2 : 99 % 2 = 1 := by norm_num

  -- 2. Indentify the smallest three-digit odd number
  have h3 : ∀ n : ℕ, n ≥ 100 → n ≥ 100 := by
    intro n hn
    exact hn

  have h4 : 100 % 2 = 0 := by norm_num

  -- 3. Find the sum of these two numbers
  norm_num
