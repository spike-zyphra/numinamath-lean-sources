import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22210 : {x : ℝ | abs (x ^ 2 + 3 * x - 4) + abs (x ^ 2 + 9 * x + 20) = 0} = {-4} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume $|x^2+3x-4|+|x^2+9x+20|=0$, then $x=-4$.
    intro h
    have h1 : abs (x ^ 2 + 3 * x - 4) ≥ 0 := by apply abs_nonneg
    have h2 : abs (x ^ 2 + 9 * x + 20) ≥ 0 := by apply abs_nonneg
    have h3 : abs (x ^ 2 + 3 * x - 4) = 0 := by
      linarith
    have h4 : x ^ 2 + 3 * x - 4 = 0 := by
      rwa [abs_eq_zero] at h3
    -- The second absolute value must also be zero
    have h5 : abs (x ^ 2 + 9 * x + 20) = 0 := by
      linarith
    have h6 : x ^ 2 + 9 * x + 20 = 0 := by
      rwa [abs_eq_zero] at h5
    have h7 : x = -4 := by
      nlinarith
    exact_mod_cast h7
  · -- Assume $x = -4$.
    intro h
    rw [h]
    norm_num [abs]