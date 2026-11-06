import Mathlib

theorem number_theory_226672 :
    {n : ℕ | let last_digit := (n^2) % 10
             let second_last_digit := ((n^2) / 10) % 10
             ((n^2) / 100) * 100 + last_digit * 10 + second_last_digit = (n + 1)^2} = 
    {13} := by
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if n satisfies the condition, then n = 13
    intro h 
    by_cases h1 : n ≤ 100
    · -- n ≤ 100
      interval_cases n <;> norm_num at h ⊢
      <;> omega
    · -- n > 100
      have h2 : n > 100 := by omega
      -- Let Y = n^2. We have Y - (Y % 100) + (Y % 10) * 10 + Y % 100 / 10 - Y ... this is messy part
      -- Try a different identity. Instead of difference which needs negatives : use positive):
      -- ((X^2 / 100 * 100) + (X^2 % 10) * 10 + ((X^2 / 10) % 10)) = X^2 + 9 * (U - T) as before
      -- Let's handle without neg
      have eq1 : ((n ^ 2) / 100) * 100 + (n ^ 2 % 10) * 10 + ((n ^ 2 / 10) % 10) = (n + 1) ^ 2 := by
        simpa using h 
      -- Maximum value of equation LHS part - n^2 ... it will be bound to 100s such that will contradict (n+1)^2 / 9
      have eq4 : ((n )^2 / 100) * 100 + (n ^ 2 % 10) * 10 + (n ^ 2 / 10 % 10) < (n ^ 2) + 100 := by
        omega 
      -- From eq4 and eq1: (n+1)^2 = LHS < n^2 + 100
      have eq5 : (n + 1) ^ 2 < (n) ^ 2 + 100 := by
        linarith [eq1, eq4] 
      -- Now we get bound on n from this quadratic
      have eq6 : 2 * n < 99 := by
        nlinarith 
      -- This contradicts n > 100
      nlinarith
  · -- Show that 13 is in the set
    intro h 
    rw [h] 
    all_goals norm_num