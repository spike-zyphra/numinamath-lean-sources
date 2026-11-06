import Mathlib

open Real
open scoped BigOperators

theorem inequalities_207075 :
  {x : ℤ | (x^2 + 6 * x + 8) * (x^2 - 4 * x + 3) < 0} = {-3, 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume (x^2 + 6 * x + 8) * (x^2 - 4 * x + 3) < 0, prove x ∈ {-3, 2}
    intro h
    have h1 : (x ^ 2 + 6 * x + 8) * (x ^ 2 - 4 * x + 3) < 0 := by linarith
    have h2 : x ≥ -4 := by
      nlinarith [sq_nonneg (x + 2 : ℤ), sq_nonneg (x + 4 : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (x - 3 : ℤ)]
    have h3 : x ≤ 3 := by
      nlinarith [sq_nonneg (x + 2 : ℤ), sq_nonneg (x + 4 : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (x - 3 : ℤ)]
    interval_cases x <;> omega
  · -- Assume x ∈ {-3, 2}, prove (x^2 + 6 * x + 8) * (x^2 - 4 * x + 3) < 0
    rintro (rfl | rfl)
    · -- Case x = -3
      norm_num
    · -- Case x = 2
      norm_num