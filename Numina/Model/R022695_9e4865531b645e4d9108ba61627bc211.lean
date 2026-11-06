import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_11022 : {c : ℝ | ∀ a b, a^2 + b^2 = 1 → c < a + b} = {c | c < -Real.sqrt 2} := by 
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume that for all a, b with a²+b²=1, we have c < a+b
    intro h
    have h1 := h (-Real.sqrt 2 / 2) (-Real.sqrt 2 / 2) (by
      have h2 : (-Real.sqrt 2 / 2: ℝ) ^2 = (0.5 : ℝ) := by
        calc
          (-Real.sqrt 2 / 2 : ℝ) ^2 = (Real.sqrt 2 / 2) ^2 := by ring_nf
          _ = (Real.sqrt 2) ^2 / 4 := by ring_nf
          _ = (2: ℝ) / 4 := by rw [Real.sq_sqrt]; positivity
          _ = (0.5: ℝ) := by norm_num
      nlinarith [h2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    )
    have h3 : (-Real.sqrt 2 / 2 : ℝ) + (-Real.sqrt 2 / 2 : ℝ) = -Real.sqrt 2 := by
      linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    linarith [h3, h1]
  · -- Assume that c < -sqrt 2.
    intro h
    intro a b h_eq
    have h3 : (a + b) ^2 ≤ (2 : ℝ) := by
      nlinarith [sq_nonneg (a - b), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h7 : (a + b) ≥ (-Real.sqrt 2) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    linarith [h, h7]