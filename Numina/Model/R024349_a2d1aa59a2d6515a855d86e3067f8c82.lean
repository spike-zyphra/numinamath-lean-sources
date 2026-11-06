import Mathlib

open Real

theorem inequalities_298577 (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (h : u * sqrt (v * w) + v * sqrt (w * u) + w * sqrt (u * v) ≥ 1) :
    u + v + w ≥ sqrt 3 := by
  have h1 : 0 < u * v * w := by
    positivity
  have h2 : 0 < v * w := by
    apply mul_pos
    linarith
    linarith
  have h3 : 0 < w * u := by
    apply mul_pos
    linarith
    linarith
  have h4 : 0 < u * v := by
    apply mul_pos
    linarith
    linarith
  have h5 : sqrt (v * w) = Real.sqrt v * Real.sqrt w := by
    rw [Real.sqrt_mul (by nlinarith)]
    all_goals nlinarith
  have h6 : sqrt (w * u) = Real.sqrt w * Real.sqrt u := by
    rw [Real.sqrt_mul (by nlinarith)]
    all_goals nlinarith
  have h7 : sqrt (u * v) = Real.sqrt u * Real.sqrt v := by
    rw [Real.sqrt_mul (by nlinarith)]
    all_goals nlinarith
  have h8 : (u + v + w) ^ 2 ≥ 3 := by
    nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt v), sq_nonneg (Real.sqrt v - Real.sqrt w), sq_nonneg (Real.sqrt w - Real.sqrt u),
      Real.sq_sqrt (show (0 : ℝ) ≤ u by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ v by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ w by linarith),
      sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u),
      Real.sqrt_nonneg u, Real.sqrt_nonneg v, Real.sqrt_nonneg w,
      h, h2, h3, h4, mul_pos hu hv, mul_pos hv hw, mul_pos hw hu, Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (u : ℝ) by linarith), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (v : ℝ) by linarith), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (w : ℝ) by linarith), sq_nonneg (Real.sqrt u * Real.sqrt v - Real.sqrt v * Real.sqrt w), sq_nonneg (Real.sqrt v * Real.sqrt w - Real.sqrt w * Real.sqrt u), sq_nonneg (Real.sqrt w * Real.sqrt u - Real.sqrt u * Real.sqrt v)]
  have h9 : u + v + w ≥ sqrt 3 := by
    have h10 : Real.sqrt ((u + v + w) ^ 2) ≥ Real.sqrt (3 : ℝ) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    have h11 : Real.sqrt ((u + v + w) ^ 2) = (u + v + w : ℝ) := by
      rw [Real.sqrt_sq (show 0 ≤ (u + v + w : ℝ) by positivity)]
    linarith [h10, h11]
  exact h9