import Mathlib

open Int

/- Problem 3. Vasya wants to find all integers $a$ such that the expression $10 n^{3}+3 n^{5}+7 a n$ is divisible by 15 for all integers $n$. What remainders can the number $a$ give when divided by 15? Provide all possible answers or prove that there are no such integers $a$. -/
theorem number_theory_242607 (a : ℤ) :
    (∀ n : ℤ, 15 ∣ 10 * n^3 + 3 * n^5 + 7 * a * n) ↔ a % 15 = 11 := by
  constructor
  -- Show that the condition implies a % 15 = 11
  · intro h
    -- By substituting n = 1, we find that 15 ∣ 13 + 7*a
    have n_eq_one : 15 ∣ 13 + 7*a := by
      have : _ := h 1
      norm_num at this
      tauto
    -- This is equivalent to a % 15 = 11 by basic modular arithmetic
    omega
  -- Show that a % 15 = 11 works
  rintro ha n
  have : n % 15 < 15 := by
    have : n % 15 < |15| := emod_lt n (show 15 ≠ 0 by positivity)
    norm_num at this
    tauto
  have : 0 ≤ n % 15 := emod_nonneg n (by positivity)
  rw [dvd_iff_emod_eq_zero]
  interval_cases this : (n % 15)
  -- Check that it works for all n mod 15
  all_goals
    rename_i h1 _
    rw [add_emod, add_emod (10*n^3), mul_emod, mul_emod (7*a), mul_emod 7, show n^3=n*n*n by ring, show n^5=n*n*n*n*n by ring, mul_emod (n*n), mul_emod n, mul_emod 3, mul_emod (n*n*n*n), mul_emod (n*n*n), mul_emod (n*n), mul_emod n, h1, ha]
    simp