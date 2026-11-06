import Mathlib

theorem inequalities_45023 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.sqrt ((z + x) * (z + y)) - z ≥ Real.sqrt (x * y) := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : 0 < (z + x) * (z + y) := by
    apply mul_pos
    all_goals
      linarith
  have h6 : Real.sqrt ((z + x) * (z + y)) = Real.sqrt (z + x) * Real.sqrt (z + y) := by
    rw [Real.sqrt_mul]
    all_goals
      nlinarith
  have h3 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
    rw [Real.sqrt_mul]
    all_goals
      nlinarith
  rw [h6, h3]
  have h7 : Real.sqrt (z + x) * Real.sqrt (z + y) ≥ Real.sqrt x * Real.sqrt y + z := by
    have hx8 : (z + x) * (z + y) ≥ (Real.sqrt x * Real.sqrt y + z)^2 := by
      nlinarith [mul_pos hz hx, mul_pos hz hy, mul_pos hx hy,
                  sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (z - Real.sqrt x * Real.sqrt y), sq_nonneg (z * (x - y)), 
                  Real.sq_sqrt (show 0 ≤ (z + x : ℝ) by positivity), 
                  Real.sq_sqrt (show 0 ≤ (z + y : ℝ) by positivity), 
                  Real.sq_sqrt (show 0 ≤ x by positivity), 
                  Real.sq_sqrt (show 0 ≤ y by positivity), 
                  mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), 
                  Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
                  mul_nonneg (show 0 ≤ z by positivity) (show 0 ≤ x by positivity), 
                  mul_nonneg (show 0 ≤ z by positivity) (show 0 ≤ y by positivity)
                ]
    have h8 : 0 ≤ Real.sqrt x * Real.sqrt y + z := by positivity
    have h9 : (Real.sqrt (z + x) * Real.sqrt (z + y)) ^ 2 ≥ (Real.sqrt x * Real.sqrt y + z)^2 := by
      calc
        (Real.sqrt (z + x) * Real.sqrt (z + y)) ^ 2 = (z + x) * (z + y) := by
          calc
            (Real.sqrt (z + x) * Real.sqrt (z + y)) ^ 2 = (Real.sqrt (z + x)) ^ 2 * (Real.sqrt (z + y)) ^ 2 := by ring
            _ = (z + x) * (z + y) := by
              rw [Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)]
        _ ≥ (Real.sqrt x * Real.sqrt y + z)^2 := hx8
    have h99 : Real.sqrt (z + x) * Real.sqrt (z + y) ≥ 0 := by positivity
    have h999 : Real.sqrt x * Real.sqrt y + z ≥ 0 := by positivity
    nlinarith [sq_nonneg (Real.sqrt (z + x) * Real.sqrt (z + y) - (Real.sqrt x * Real.sqrt y + z)), h9, Real.sqrt_nonneg (z + x), Real.sqrt_nonneg (z + y), 
                Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
                mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (z + y)), 
                mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
              ]
  linarith