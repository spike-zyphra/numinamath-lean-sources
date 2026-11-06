import Mathlib

theorem inequalities_307926 (a : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → 3 * x + 4 * Real.sqrt (x * y) ≤ a * (x + y)) ↔
    a ≥ 4 := by
  constructor
  · -- Forward direction: if the inequality holds for all x, y > 0, then a ≥ 4
    intro h
    have h1 := h 4 1 (by norm_num) (by norm_num)
    have h2 : Real.sqrt ((4 : ℝ) * (1 : ℝ)) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h2] at h1
    nlinarith
  · -- Backward direction: if a ≥ 4, then the inequality holds for all x, y > 0
    intro ha x y hx hy
    have h2 : 3 * x + 4 * Real.sqrt (x * y) ≤ 4 * (x + y) := by
      have hxy : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
        rw [Real.sqrt_mul]
        all_goals positivity
      rw [hxy]
      nlinarith [sq_nonneg (Real.sqrt x - 2 * Real.sqrt y),
        Real.sq_sqrt (show (0 : ℝ) ≤ x by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ y by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (x) by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (y) by positivity),
        mul_pos hx hy,
        Real.sqrt_nonneg x,
        Real.sqrt_nonneg y]
    have h3 : 4 * (x + y) ≤ a * (x + y) := by
      nlinarith [ha, show (x + y) > 0 by linarith, mul_pos hx hy]
    linarith [h2, h3]