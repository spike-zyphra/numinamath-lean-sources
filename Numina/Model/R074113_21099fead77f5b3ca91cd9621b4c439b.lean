import Mathlib

theorem number_theory_101675 (n : ℤ) : 6 ∣ n^3 + 5 * n := by 
  have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases h1 with (h | h | h | h | h | h) <;> ( 
    -- For each case compute $n^3 + 5n$ modulo 6.
    -- Case 1: n % 6 = 0.
    -- Case 2: n % 6 = 1.
    -- Case 3: n % 6 = 2.
    -- Case 4: n % 6 = 3.
    -- Case 5: n % 6 = 4.
    -- Case 6: n % 6 = 5.
    simp [Int.dvd_iff_emod_eq_zero, pow_three, Int.add_emod, Int.mul_emod, h] <;> omega
  )
  all_goals 
    omega