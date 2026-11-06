import Mathlib

open Real Set

theorem algebra_243657 {f : ℝ → ℝ} (hf : f = fun a => a^3 - a^2 - 2 * sqrt a) :
    IsLeast {x | ∃ a, x = f a ∧ a ≥ 0} (f 1) := by
  constructor
  · -- Show f(1) is in the image
    use 1
    all_goals
    norm_num [hf, sqrt_eq_iff_sq_eq]
  · -- Show f(1) ≤ f(a) for all a ≥ 0
    intro x hx
    rcases hx with ⟨a, ha_eq, ha_nonneg⟩
    have h2 : f 1 = -2 := by
      rw [hf]
      have h3 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      simp [h3]
      all_goals
      linarith
    have h3 : f a = a ^ 3 - a ^ 2 - 2 * sqrt a := by
      rw [hf]
    rw [ha_eq, h3] at *
    have h4 : a ≥ 0 := by linarith [ha_nonneg]
    have h6 : a ^ 3 - a ^ 2 - 2 * sqrt a ≥ -2 := by
      have h4 : a ≥ 0 := by linarith [ha_nonneg]
      have h5 : sqrt a ≥ 0 := Real.sqrt_nonneg a
      by_cases h : a ≤ 1
      · -- Assume a ≤1
        nlinarith [sq_nonneg (a - 1), sq_nonneg (sqrt a - 1), Real.sqrt_nonneg a, 
                  Real.sq_sqrt (show 0 ≤ a by linarith), 
                  sq_nonneg ((sqrt a) ^ 2 - 1), 
                  mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ a by linarith),
                  Real.sq_sqrt (show 0 ≤ a by linarith),
                  sq_nonneg (a - 1), sq_nonneg ((sqrt a) ^ 2 -1), sq_nonneg (sqrt a -1)
                  ]
      · -- Assume a >1
        have ha : a ≥ 1 := by linarith
        have h7 : sqrt a ≥ 1 := by 
          have hk1 : sqrt a ≥ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
          have hk2 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
          linarith [hk1, hk2]
        nlinarith [sq_nonneg (a - 1), sq_nonneg (sqrt a - 1), Real.sqrt_nonneg a, 
                  Real.sq_sqrt (show 0 ≤ a by linarith), 
                  sq_nonneg ((sqrt a) ^ 2 - 1), 
                  Real.sq_sqrt (show 0 ≤ a by linarith),
                  sq_nonneg (a - 1), sq_nonneg ((sqrt a) ^ 2 -1), sq_nonneg (sqrt a -1)
                  ]
    linarith [h2, h6]