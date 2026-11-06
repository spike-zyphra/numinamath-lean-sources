import Mathlib

theorem algebra_21291 (x : ℝ) : x ≥ 0 ∧ Real.sqrt (5 * x) * Real.sqrt (10 * x) * Real.sqrt (18 * x) = 30 ↔ x = 1 := by
  constructor
  · -- Forward direction: if $x ≥ 0 ∧ Real.sqrt (5 * x) * Real.sqrt (10 * x) * Real.sqrt (18 * x) = 30$, then $x = 1$.
    intro h
    rcases h with ⟨hx1, heq⟩
    have h2 : Real.sqrt (5 * x) * Real.sqrt (10 * x) * Real.sqrt (18 * x) = Real.sqrt ((5 * x) * (10 * x) * (18 * x)) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      all_goals nlinarith [show (5 * x) ≥ 0 by nlinarith, show (10 * x) ≥ 0 by nlinarith, show (18 * x) ≥ 0 by nlinarith]
    rw [h2] at heq 
    have h3 : (5 * x) * (10 * x) * (18 * x) = (900 : ℝ) * (x ^ 3) := by 
      ring_nf
    have heq2 : Real.sqrt ((5 * x) * (10 * x) * (18 * x)) = Real.sqrt ((900 : ℝ) * (x ^ 3)) := by
      rw [h3]
    rw [heq2] at heq 
    have h4 : Real.sqrt ((900 : ℝ) * (x ^ 3)) ^ 2 = 30 ^ 2 := by
      nlinarith [heq]
    have h5 : Real.sqrt ((900 : ℝ) * (x ^ 3)) ^ 2 = (900 : ℝ) * (x ^ 3) := by
      have pos1 : (900 : ℝ) * (x ^ 3) ≥ 0 := by nlinarith [show x ≥ 0 by linarith, sq_nonneg (x ^ 2)]
      rw [Real.sq_sqrt pos1]
    rw [h5] at h4
    have h6 : x ^ 3 = 1 := by
      nlinarith [h4, show 900 > (0 : ℝ) by norm_num]
    have h7 : x = 1 := by
      have h8 : x ^ 3 - 1 = 0 := by linarith
      have h9 : (x - 1) * (x ^ 2 + x + 1) = 0 := by
        nlinarith [h8]
      cases' (mul_eq_zero.1 h9) with h10 h11
      · 
        linarith 
      · 
        nlinarith [sq_nonneg (x + 1 / 2)]
    tauto
  · -- Backward direction: if $x = 1$, then $x ≥ 0 ∧ Real.sqrt (5 * x) * Real.sqrt (10 * x) * Real.sqrt (18 * x) = 30$.
    intro heq
    rw [heq] 
    constructor
    · norm_num
    · -- Show $\sqrt{5 * 1} * \sqrt{10 * 1} * \sqrt{18 * 1} = 30$
      have h2 : Real.sqrt (5 * (1 : ℝ)) * Real.sqrt (10 * (1 : ℝ)) * Real.sqrt (18 * (1 : ℝ)) = Real.sqrt ((5 * (1 : ℝ)) * (10 * (1 : ℝ)) * (18 * (1 : ℝ))) := by
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        all_goals norm_num
      rw [h2]
      have h4 : (5 * (1 : ℝ)) * (10 * (1 : ℝ)) * (18 * (1 : ℝ)) = (900 : ℝ) := by
        norm_num
      rw [h4]
      have h6 : Real.sqrt ((900 : ℝ) ) = (30 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [h6, Real.sqrt_nonneg ((900 : ℝ)), Real.sqrt_nonneg ((5 * (1 : ℝ)) * (10 * (1 : ℝ)) * (18 * (1 : ℝ)))]