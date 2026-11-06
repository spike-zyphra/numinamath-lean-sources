import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

theorem sum_of_tens_in_100_to_10 : (100 ^ 10 : ℕ) / 10 = 10 ^ 19 := by
  -- Step 1 and 2: Express 100^10 as (10^2)^10
  have h1 : (100 : ℕ) = 10^2 := by norm_num

  -- Step 3: Simplify (10^2)^10 to 10^20
  have h2 : (100 : ℕ) ^ 10 = 10^20 := by
    calc (100 : ℕ) ^ 10
      = (10^2)^10 := by rw [h1]
      _ = 10^(2*10) := by simp [pow_mul]
      _ = 10^20 := by ring_nf

  -- Step 4 and 5: Express 10^20 as 10 * 10^19
  have h3 : (10^20 : ℕ) = 10 * 10^19 := by ring

  -- Step 6: Divide both sides by 10
  calc (100 : ℕ) ^ 10 / 10
    = 10^20 / 10 := by rw [h2]
    _ = (10 * 10^19) / 10 := by rw [h3]
    _ = 10^19 := by norm_num

/-- If the number $100^ {10}$  is written as the sum of tens, how many terms will there be? -/
theorem Arithmetic_4183 : (100 ^ 10 : ℕ) / 10 = 10 ^ 19 :=
  sum_of_tens_in_100_to_10
