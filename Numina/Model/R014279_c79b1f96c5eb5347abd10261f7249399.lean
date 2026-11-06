import Mathlib

theorem number_theory_232738 : ¬Prime (2011 * 2012 * 2013 * 2014 + 1) := by
  have h1 : (2011 * 2012 * 2013 * 2014 + 1 : ℕ) = (4050155 : ℕ) ^ 2 := by
    norm_num
  rw [h1]
  apply not_prime_pow
  all_goals norm_num