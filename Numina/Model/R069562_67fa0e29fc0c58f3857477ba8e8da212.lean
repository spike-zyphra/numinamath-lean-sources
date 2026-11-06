import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_325719 : orderOf (I : ℂ) = 4 := by
  have h2 : I ^ 4 = 1 := by
    norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
    
  have h3 : ∀ r < 4, r > 0 → I ^ r ≠ 1 := by
    intro r hr1 hr2
    interval_cases r <;> norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I] at *
  
  -- We now apply the definition of the order of an element in a group
  rw [orderOf_eq_iff] <;> simp [h2, h3]
  -- Lean confirms that the order of I is indeed 4
  <;> try { tauto }