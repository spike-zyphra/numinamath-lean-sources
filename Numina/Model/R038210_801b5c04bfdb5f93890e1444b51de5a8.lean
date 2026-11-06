import Mathlib

theorem algebra_316590 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : 1949 / y ^ 2 = 2007 / x ^ 2) (h2 : 1 / x + 1 / y = 1) :
    Real.sqrt (1949 * x + 2007 * y) = Real.sqrt 1949 + Real.sqrt 2007 := by

  have h3 : 1949 * x ^ 2 = 2007 * y ^ 2 := by 
    field_simp at h1
    nlinarith [h1]

  have h4 : x * y = x + y := by 
    field_simp at h2
    nlinarith [h2]

  have eq1 : Real.sqrt 1949 * x = Real.sqrt 2007 * y := by
    have eq2 : 1949 * x ^ 2 = 2007 * y ^ 2 := h3
    have eq3 : (Real.sqrt 1949 * x) ^ 2 = (Real.sqrt 2007 * y) ^ 2 := by
      have eq4 : (Real.sqrt 1949 * x) ^ 2 = Real.sqrt 1949 ^ 2 * x ^ 2 := by ring
      have eq5 : (Real.sqrt 2007 * y) ^ 2 = Real.sqrt 2007 ^ 2 * y ^ 2 := by ring
      rw [eq4, eq5]
      have h9 : Real.sqrt 1949 ^ 2 = 1949 := Real.sq_sqrt (by norm_num)
      have h10 : Real.sqrt 2007 ^ 2 = 2007 := Real.sq_sqrt (by norm_num)
      rw [h9, h10]
      linarith
    have eq4 : 0 ≤ Real.sqrt 1949 * x := by
      positivity
    have eq5 : 0 ≤ Real.sqrt 2007 * y := by
      positivity
    nlinarith [sq_nonneg (Real.sqrt 1949 * x - Real.sqrt 2007 * y)]

  have h5 : 1949 * x + 2007 * y = (Real.sqrt 1949 + Real.sqrt 2007) ^ 2 := by
    have eq7 : Real.sqrt 1949 * x = Real.sqrt 2007 * y := eq1
    have h9 : Real.sqrt 1949 ^ 2 = 1949 := Real.sq_sqrt (by norm_num)
    have h10 : Real.sqrt 2007 ^ 2 = 2007 := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg (x - y), sq_nonneg (Real.sqrt 1949 - Real.sqrt 2007), 
      mul_pos hx hy, mul_pos hx (show Real.sqrt 1949 > 0 by positivity), 
      mul_pos hx (show Real.sqrt 2007 > 0 by positivity), 
      mul_pos hy (show Real.sqrt 1949 > 0 by positivity), 
      mul_pos hy (show Real.sqrt 2007 > 0 by positivity), 
      mul_nonneg (Real.sqrt_nonneg 1949) (Real.sqrt_nonneg 2007)
      ]

  have h7 : Real.sqrt (1949 * x + 2007 * y) = Real.sqrt 1949 + Real.sqrt 2007 := by
    rw [h5]
    have h9 : Real.sqrt ((Real.sqrt 1949 + Real.sqrt 2007) ^ 2) = Real.sqrt 1949 + Real.sqrt 2007 := by
      rw [Real.sqrt_sq]
      positivity
    linarith [h9]

  exact h7