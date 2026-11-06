import Mathlib
open Real

/- √8+ √18=
(A) √20 (B) 2(√2 + √3) (C) 7 (D) 5√2 (E) 2√13 -/
theorem algebra_96109 : Real.sqrt 8 + Real.sqrt 18 = 5 * Real.sqrt 2 := by
  -- solve by expanding the square roots into products of √2
  -- that is, √8=2√2 and √18=3√2
  -- this can be done by squaring the both side of the equalities and check the results of both side are the same.
  rw [show Real.sqrt 8 = 2 * Real.sqrt 2 by
  rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num ; ring_nf ; norm_num]
  rw [show Real.sqrt 18 = 3 * Real.sqrt 2 by
  rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num ; ring_nf ; norm_num]
  ring