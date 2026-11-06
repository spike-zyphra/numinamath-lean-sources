import Mathlib

open Real

theorem inequalities_323618 (a : ℝ) (ha : a > 0) :
    (∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ a * sqrt (x + y)) ↔
    a ≥ sqrt 2 := by
  constructor
  · -- (∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ a * sqrt (x + y)) → a ≥ sqrt 2
    intro h
    have h1 := h 1 1 (by norm_num) (by norm_num)
    have h1' : sqrt (1 : ℝ) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt (1 + (1 : ℝ)) = sqrt (2 : ℝ) := by norm_num
    simp [h1', h2] at h1
    by_contra h3
    have h4 : a < sqrt 2 := by linarith
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)), h4]
  · -- a ≥ sqrt 2 → (∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ a * sqrt (x + y))
    intro h x y hx hy
    have h1 : sqrt x + sqrt y ≤ Real.sqrt 2 * sqrt (x + y) := by
      have h1 : (sqrt x + sqrt y) ^ 2 ≤ 2 * (x + y) := by
        have h2 : (sqrt x + sqrt y) ^ 2 = (sqrt x) ^ 2 + (sqrt y) ^ 2 + 2 * (sqrt x * sqrt y) := by
          ring
        have h3 : (sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
        have h4 : (sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)
        rw [h2, h3, h4]
        nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y,
          sq_nonneg (sqrt x - sqrt y),
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y),
          pow_two_nonneg (sqrt x - sqrt y)
        ]
      have h1' : (Real.sqrt 2 * sqrt (x + y)) ^ 2 = 2 * (x + y) := by
        calc
          (Real.sqrt 2 * sqrt (x + y)) ^ 2 = (Real.sqrt 2) ^ 2 * (sqrt (x + y)) ^ 2 := by ring
          _ = 2 * (x + y) := by
            have h21 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
            have h22 : (sqrt (x + y)) ^ 2 = x + y := by
              apply Real.sq_sqrt
              linarith
            rw [h21, h22]
            <;> nlinarith
      have h11 : sqrt x + sqrt y ≥ 0 := by
        have h10 : sqrt x ≥ 0 := Real.sqrt_nonneg x
        have h11 : sqrt y ≥ 0 := Real.sqrt_nonneg y
        linarith
      have h12 : Real.sqrt 2 * sqrt (x + y) ≥ 0 := by
        have h10 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
        have h11 : sqrt (x + y) ≥ 0 := Real.sqrt_nonneg (x + y)
        nlinarith
      nlinarith [Real.sqrt_nonneg (x + y), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt x - sqrt y), Real.sq_sqrt (show (0 : ℝ) ≤ (x + y : ℝ) by positivity) ]
    have h2 : a * sqrt (x + y) ≥ Real.sqrt 2 * sqrt (x + y) := by
      have h4 : a ≥ Real.sqrt 2 := h
      have h5 : sqrt (x + y) ≥ 0 := Real.sqrt_nonneg (x + y)
      nlinarith
    linarith [h1, h2]