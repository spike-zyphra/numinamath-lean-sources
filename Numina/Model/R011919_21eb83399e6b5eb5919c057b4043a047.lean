import Mathlib

open Int


theorem quadratic_prime_roots_result :
  ∃ (a b : ℤ), (∃ x1 x2 : ℤ, Prime x1 ∧ Prime x2 ∧ x1 ≠ x2 ∧
    a * x1^2 + b * x1 - 2008 = 0 ∧
    a * x2^2 + b * x2 - 2008 = 0) ∧
    3 * a + b = 1000 := by 
  use -4, 1012
  constructor
  · -- Show that there exists integers x1, x2 such that they are primes, distinct and solutions
    use 2, 251
    have h1 : Prime (2 : ℤ) := by
      norm_num
    have h2 : Prime (251 : ℤ) := by
      norm_num
    have h3 : (2 : ℤ) ≠ (251 : ℤ) := by
      norm_num
    have h4 : (-4 : ℤ) * (2 : ℤ) ^ 2 + (1012 : ℤ) * (2 : ℤ) - 2008 = (0 : ℤ) := by
      norm_num
    have h5 : (-4 : ℤ) * (251 : ℤ) ^ 2 + (1012 : ℤ) * (251 : ℤ) - 2008 = (0 : ℤ) := by
      norm_num
    exact ⟨h1, h2, h3, h4, h5⟩
  · -- Show that 3 * a + b = 1000.
    norm_num