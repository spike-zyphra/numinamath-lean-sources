import Mathlib

open Real

theorem inequalities_11138 (k : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ k * sqrt (5 * x + y)) ↔
    k ≥ sqrt 30 / 5 := by 
  constructor
  · -- Assume inequality holds for all x > 0, y > 0, prove k ≥ sqrt 30 / 5
    intro hk
    have h1 := hk (1 / 30) (5 / 6) (by norm_num) (by norm_num)
    have h2 : sqrt (1 / 30 : ℝ) + sqrt (5 / 6 : ℝ) = sqrt 30 / 5 := by
      have h3 : sqrt (1 / 30 : ℝ) = 1 / sqrt 30 := by
        field_simp
        <;> rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h4 : sqrt (5 / 6 : ℝ) = (sqrt 30) / 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h3, h4]
      field_simp [show sqrt 30 > 0 by positivity]
      <;> ring_nf <;> norm_num
      <;> linarith [Real.sqrt_nonneg 30, Real.sq_sqrt (show (0 : ℝ) ≤ 30 by norm_num)]
    have h3 : sqrt (5 * (1 / 30 : ℝ) + (5 / 6 : ℝ)) = 1 := by
      rw [show 5 * (1 / 30 : ℝ) + (5 / 6 : ℝ) = (1 : ℝ) by norm_num]
      simp
    rw [h3, h2] at h1
    linarith
  · -- Assume k ≥ sqrt 30 / 5, prove inequality for all x > 0, y > 0
    intro hk x y hx hy
    have h1 : sqrt x + sqrt y ≤ (sqrt 30 / 5) * sqrt (5 * x + y) := by
      have h2 : (sqrt x + sqrt y) ^ 2 ≤ (30 / 25) * (5 * x + y) := by
        nlinarith [sq_nonneg (sqrt x - 1 / 5 * sqrt y), sq_nonneg (5 * sqrt x - sqrt y), 
          Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y by linarith), 
          Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
          ]
      have h3 : sqrt x + sqrt y ≤ Real.sqrt ((30 / 25) * (5 * x + y)) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      have h4 : Real.sqrt ((30 / 25) * (5 * x + y)) = (Real.sqrt 30 / 5) * Real.sqrt (5 * x + y) := by
        have h7 : Real.sqrt ((30 / 25) * (5 * x + y)) = Real.sqrt (30 / 25) * Real.sqrt (5 * x + y) := by
          rw [Real.sqrt_mul]
          positivity
        have h8 : Real.sqrt (30 / 25 : ℝ) = Real.sqrt 30 / 5 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h7, h8]
      linarith [h3, h4]
    have h4 : (sqrt 30 / 5) * sqrt (5 * x + y) ≤ k * sqrt (5 * x + y) := by
      have h5 : sqrt (5 * x + y) ≥ 0 := by positivity
      have h6 : sqrt 30 / 5 ≤ k := by linarith [hk]
      nlinarith
    linarith [h1, h4]