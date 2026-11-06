import Mathlib

theorem algebra_18964 : {k : ℝ | (13 - Real.sqrt 131) / 4 ∈ {x | 2 * x ^ 2 - 13 * x + k = 0}} = {((19:ℝ) / 4)} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (13 - Real.sqrt 131) / 4 is a root of 2x^2 - 13x + k = 0, prove k = 19/4
    intro h
    have h_eq : 2 * ((13 - Real.sqrt 131) / 4) ^ 2 - 13 * ((13 - Real.sqrt 131) / 4) + k = 0 := by
      simpa using h
    nlinarith [Real.sqrt_pos.mpr (show (131 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (131 : ℝ) by norm_num), Real.sqrt_nonneg 131, Real.sq_sqrt (show (0 : ℝ) ≤ (131 : ℝ) by norm_num)]
  · -- Assume k = 19/4, prove (13 - Real.sqrt 131) / 4 is a root
    intro h_eq
    rw [h_eq]
    have h_eq : 2 * ((13 - Real.sqrt 131) / 4) ^ 2 - 13 * ((13 - Real.sqrt 131) / 4) + (19 / 4 : ℝ) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (131 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (131 : ℝ) by norm_num), Real.sqrt_nonneg 131, Real.sq_sqrt (show (0 : ℝ) ≤ (131 : ℝ) by norm_num)]
    simpa using h_eq