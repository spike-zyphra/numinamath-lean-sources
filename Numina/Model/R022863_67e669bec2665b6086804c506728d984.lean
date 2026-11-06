import Mathlib

theorem inequalities_324705 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 3) :
    Real.sqrt x + Real.sqrt y + Real.sqrt z ≥ x * y + y * z + z * x := by 
  have h1 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h2 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have h3 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z

  have h4 : Real.sqrt x ^2 = x := Real.sq_sqrt (by linarith)
  have h5 : Real.sqrt y ^2 = y := Real.sq_sqrt (by linarith)
  have h6 : Real.sqrt z ^2 = z := Real.sq_sqrt (by linarith)

  have h7 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
  have h8 : Real.sqrt y ≥ 0 := Real.sqrt_nonneg y
  have h9 : Real.sqrt z ≥ 0 := Real.sqrt_nonneg z
  
  nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt y - 1), sq_nonneg (Real.sqrt z - 1),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          Real.sq_sqrt (show 0 ≤ x by linarith),
          Real.sq_sqrt (show 0 ≤ y by linarith),
          Real.sq_sqrt (show 0 ≤ z by linarith),
          hsum,
          mul_nonneg h7 h8,
          mul_nonneg h8 h9,
          mul_nonneg h7 h9,
          mul_nonneg hx hy,
          mul_nonneg hy hz,
          mul_nonneg hx hz
        ]