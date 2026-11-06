import Mathlib

open scoped BigOperators

theorem inequalities_205702 {x : ℚ} :
  (∑ i in Finset.range 102, x^(2 * i)) - 102 * x^101 ≥ 0 := by
  have h1 : (∑ i in Finset.range 102, x ^ (2 * i)) - 102 * x ^ 101 = 
      (∑ i in Finset.range 51, ((x ^ (i) - x ^ (101 - i)) ^ 2)) := by
    simp [Finset.sum_range_succ]
    ring_nf
  rw [h1]
  have h2 : (∑ i in Finset.range 51, ((x ^ (i) - x ^ (101 - i)) ^ 2)) ≥ 0 := by
    apply Finset.sum_nonneg
    intro i hi
    have h3 : ((x ^ (i) - x ^ (101 - i)) ^ 2) ≥ 0 := by
      apply sq_nonneg
    simpa using h3
  exact h2