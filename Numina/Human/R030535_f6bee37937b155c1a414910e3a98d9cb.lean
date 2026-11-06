import Mathlib

/- Show that the equation \(a^3+(a+1)^3+\ldots+(a+6)^3=b^4+(b+1)^4\) has no solutions in integers \(a,b\).-/
theorem number_theory_8576 (a b : ℤ) : ∑ i ∈ Finset.range 7, (a + i) ^ 3 ≠ b ^ 4 + (b + 1) ^ 4 := by
  -- Lemma: x^n % 7 = (x % 7)^n % 7
  have pow_mod7 (x : ℤ) (n : ℕ) : (x ^ n) % 7 = ((x % 7) ^ n) % 7 := by
    induction' n with n ih
    . simp
    conv =>
      congr
      . rw [pow_succ, Int.mul_emod, ih]
      rw [pow_succ, Int.mul_emod, Int.emod_emod]
  -- We show that LHS ≠ RHS as the LHS equals zero mod7, but the RHS does not equal to zero mod7.
  have ne_of_mod7 (x y : ℤ) (hx : x % 7 = 0) (hy : y % 7 ≠ 0) : x ≠ y := by
    intro hxy
    norm_num [← hxy, hx] at hy
  apply ne_of_mod7
  -- Show that RHS does not equal to zero mod7 by checking all possible value mod7.
  . rw [Int.add_emod, pow_mod7, pow_mod7 (b + 1), Int.add_emod b 1]
    have : 0 ≤ b % 7 := Int.emod_nonneg _ (by norm_num)
    have : b % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases b % 7
    all_goals norm_num
  -- Show that LHS equal to zero mod7 by checking all possible value mod7.
  rw [Finset.sum_int_mod, Finset.sum_range_succ, pow_mod7, Int.add_emod a (6 : ℕ),
    Finset.sum_range_succ, pow_mod7, Int.add_emod a (5 : ℕ),
    Finset.sum_range_succ, pow_mod7, Int.add_emod a (4 : ℕ),
    Finset.sum_range_succ, pow_mod7, Int.add_emod a (3 : ℕ),
    Finset.sum_range_succ, pow_mod7, Int.add_emod a (2 : ℕ),
    Finset.sum_range_succ, pow_mod7, Int.add_emod a (1 : ℕ),
    Finset.sum_range_succ, pow_mod7, Int.add_emod a (0 : ℕ),
    Finset.range_zero, Finset.sum_empty, zero_add]
  have : 0 ≤ a % 7 := Int.emod_nonneg _ (by norm_num)
  have : a % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases a % 7
  all_goals norm_num
