import Mathlib

theorem inequalities_265564 (a : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → Real.sqrt x + Real.sqrt y ≤ a * Real.sqrt (x + y)) ↔
    a ≥ Real.sqrt 2 := by
  constructor
  · -- Forward direction: assuming the inequality holds for all positive (x, y), proving (a >= sqrt 2)
    intro h
    have h11 := h 1 1 (by norm_num) (by norm_num)
    have h21 : Real.sqrt 1 + Real.sqrt 1 ≤ a * Real.sqrt (1 + 1) := by simpa using h11
    have h31 : Real.sqrt 1 = 1 := Real.sqrt_one
    have h41 : Real.sqrt (1 + 1) = Real.sqrt (2 : ℝ) := by norm_num
    rw [h31, h41] at h21
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 1, Real.sqrt_nonneg 1, sq_nonneg (a - Real.sqrt 2), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
  · -- Backward direction: proving the inequality holds for all positive x, y
    intro ha x y hx hy
    have h1 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
    have h2 : Real.sqrt y ≥ 0 := Real.sqrt_nonneg y
    have h3 : Real.sqrt (x + y) ≥ 0 := Real.sqrt_nonneg (x + y)
    have h4 : (Real.sqrt x + Real.sqrt y) ^ 2 ≤ (a * Real.sqrt (x + y)) ^ 2 := by
      have he1 : (Real.sqrt x + Real.sqrt y) ^ 2 = x + y + 2 * (Real.sqrt x * Real.sqrt y) := by
        calc
          (Real.sqrt x + Real.sqrt y) ^ 2
              = (Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) := by ring
          _ = x + y + 2 * (Real.sqrt x * Real.sqrt y) := by
            have h9 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
            have h10 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)
            rw [h9, h10]
      have he2 : (a * Real.sqrt (x + y)) ^ 2 = a ^ 2 * (Real.sqrt (x + y) ^ 2) := by
        ring
      have he3 : Real.sqrt (x + y) ^ 2 = x + y := Real.sq_sqrt (show (0 : ℝ) ≤ (x + y : ℝ) by linarith)
      rw [he2, he3]
      have h10 : 2 * (Real.sqrt x * Real.sqrt y) ≤ x + y := by
        have h11 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
        have h12 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)
        nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sqrt_nonneg x, Real.sqrt_nonneg y, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
      have h7 : a ^ 2 ≥ 2 := by nlinarith [Real.sqrt_nonneg 2, sq_nonneg (a - Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), ha, Real.sqrt_nonneg 2, sq_nonneg a, Real.sqrt_nonneg a]
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg (x + y), h7, Real.sq_sqrt (show x ≥ 0 by linarith), Real.sq_sqrt (show y ≥ 0 by linarith), Real.sq_sqrt (show x + y ≥ 0 by linarith)]
    have h5 : Real.sqrt x + Real.sqrt y ≥ 0 := by positivity
    have h6 : a * Real.sqrt (x + y) ≥ 0 := by
      have ha2 : a ≥ 0 := by
        nlinarith [show Real.sqrt 2 ≥ 0 by positivity, ha]
      have h7 : Real.sqrt (x + y) ≥ 0 := Real.sqrt_nonneg (x + y)
      nlinarith [ha2, h7]
    have h7 : Real.sqrt x + Real.sqrt y ≤ a * Real.sqrt (x + y) := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg (x + y), 
        sq_nonneg (Real.sqrt x + Real.sqrt y - a * Real.sqrt (x + y)), 
        sq_nonneg (a), 
        sq_nonneg (a - Real.sqrt 2), 
        Real.sqrt_nonneg (2 : ℝ), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x + y : ℝ) by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (y : ℝ) by linarith)
      ]
    exact h7