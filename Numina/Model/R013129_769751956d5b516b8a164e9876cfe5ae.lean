import Mathlib

open Real

theorem inequalities_217724 (lambda : ℝ) :
    (∀ u v w : ℝ, u > 0 → v > 0 → w > 0 →
      u * sqrt (v * w) + v * sqrt (w * u) + w * sqrt (u * v) ≥ 1 →
        u + v + w ≥ lambda) ↔
    lambda ≤ sqrt 3 := by

  constructor
  · -- Assume that the inequality holds for all positive u, v, w, prove that λ ≤ √3
    intro h
    have h1 := h (sqrt 3 / 3) (sqrt 3 / 3) (sqrt 3 / 3) (by positivity) (by positivity) (by positivity)
    have h2 : (sqrt 3 / 3 : ℝ) * sqrt ((sqrt 3 / 3 : ℝ) * (sqrt 3 / 3 : ℝ)) + (sqrt 3 / 3 : ℝ) * sqrt ((sqrt 3 / 3 : ℝ) * (sqrt 3 / 3 : ℝ)) + (sqrt 3 / 3 : ℝ) * sqrt ((sqrt 3 / 3 : ℝ) * (sqrt 3 / 3 : ℝ)) ≥ 1 := by
      have h3 : sqrt ((sqrt 3 / 3 : ℝ) * (sqrt 3 / 3 : ℝ)) = (sqrt 3 / 3 : ℝ) := by
        have h4 : (sqrt 3 / 3 : ℝ) * (sqrt 3 / 3 : ℝ) = (1 / 3 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        rw [h4]
        have h5 : sqrt (1 / 3 : ℝ) = (sqrt 3 / 3 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        linarith [h5]
      rw [h3]
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h3 : (sqrt 3 / 3 : ℝ) + (sqrt 3 / 3 : ℝ) + (sqrt 3 / 3 : ℝ) = sqrt 3 := by
      ring_nf
    have h4 := h1 h2
    rw [h3] at h4
    linarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  · -- Assume that λ ≤ √3, prove that the inequality holds for all positive u, v, w
    intro h u v w hu hv hw ha
    have h2 : (u + v + w) ^ 2 ≥ 3 * (u * v + u * w + v * w) := by
      nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (u - w)]
    have h3 : u * v + u * w + v * w ≥ 1 := by
      have h4 : u * sqrt (v * w) + v * sqrt (w * u) + w * sqrt (u * v) ≤ u * v + u * w + v * w := by
        have h5 : sqrt (v * w) ≤ (v + w) / 2 := by
          nlinarith [sq_nonneg (v - w), Real.sqrt_nonneg (v * w), Real.sq_sqrt (show 0 ≤ (v * w : ℝ) by positivity)]
        have h6 : sqrt (w * u) ≤ (w + u) / 2 := by
          nlinarith [sq_nonneg (w - u), Real.sqrt_nonneg (w * u), Real.sq_sqrt (show 0 ≤ (w * u : ℝ) by positivity)]
        have h7 : sqrt (u * v) ≤ (u + v) / 2 := by
          nlinarith [sq_nonneg (u - v), Real.sqrt_nonneg (u * v), Real.sq_sqrt (show 0 ≤ (u * v : ℝ) by positivity)]
        have h8 : u * sqrt (v * w) + v * sqrt (w * u) + w * sqrt (u * v) ≤ u * ((v + w) / 2) + v * ((w + u) / 2) + w * ((u + v) / 2) := by
          have h9 : u * sqrt (v * w) ≤ u * ((v + w) / 2) := by
            apply mul_le_mul_of_nonneg_left h5 (by linarith)
          have h10 : v * sqrt (w * u) ≤ v * ((w + u) / 2) := by
            apply mul_le_mul_of_nonneg_left h6 (by linarith)
          have h11 : w * sqrt (u * v) ≤ w * ((u + v) / 2) := by
            apply mul_le_mul_of_nonneg_left h7 (by linarith)
          linarith [h9, h10, h11]
        linarith
      linarith [ha, h4]
    have h4 : (u + v + w) ^ 2 ≥ 3 := by
      nlinarith [h2, h3, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h5 : u + v + w ≥ Real.sqrt 3 := by
      have h6 : (u + v + w : ℝ) ^ 2 ≥ (3 : ℝ) := by
        linarith [h4]
      have h7 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      nlinarith [Real.sqrt_nonneg 3, show (0 : ℝ) ≤ (u + v + w) by positivity]
    linarith [h5, h, Real.sqrt_nonneg 3]