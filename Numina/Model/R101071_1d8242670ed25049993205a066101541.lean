import Mathlib

open Real Set

theorem inequalities_10957 (k : ℝ) :
    (∃ x : ℝ, x ∈ Icc 0 2 ∧ sqrt x + sqrt (2 - x) ≥ k) ↔ k ≤ 2 := by
  constructor
  · -- Assume there exists an x in [0, 2] satisfying the inequality
    rintro ⟨x, ⟨hx1, hx2⟩, h⟩
    have h1 : sqrt x ≥ 0 := Real.sqrt_nonneg x
    have h2 : sqrt (2 - x) ≥ 0 := Real.sqrt_nonneg (2 - x)
    nlinarith [sq_nonneg (sqrt x - sqrt (2 - x)), sq_nonneg (sqrt x - 1), sq_nonneg (sqrt (2 - x) - 1), sq_nonneg (x - 1), 
      Real.sq_sqrt (show 0 ≤ x by linarith [hx1, hx2]), Real.sq_sqrt (show 0 ≤ (2 : ℝ) - x by linarith [hx1, hx2]), 
      Real.sqrt_nonneg x, Real.sqrt_nonneg (2 - x), 
      Real.sqrt_le_sqrt (show 0 ≤ (2 - x) by linarith [hx1, hx2]), 
      Real.sqrt_le_sqrt (show 0 ≤ x by linarith [hx1, hx2]), 
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (2 - x))]
  · -- Assume k ≤ 2, prove existence of x in [0, 2] such that sqrt(x) + sqrt(2 - x) ≥ k
    intro hk
    use 1
    constructor
    · -- Show that 1 ∈ [0, 2]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that sqrt (1) + sqrt (2 - 1) ≥ k
      have h1 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      have h2 : sqrt (2 - (1 : ℝ)) = 1 := by
        rw [show (2 - (1 : ℝ)) = 1 by norm_num]
        exact Real.sqrt_one
      linarith [h1, h2, hk]