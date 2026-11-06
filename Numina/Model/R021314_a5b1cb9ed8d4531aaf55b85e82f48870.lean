import Mathlib

theorem algebra_325620 (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y)
    (h1 : a + b + 1 / a + 9 / b = 8) (h2 : a * x ^ 2 + b * y ^ 2 = 18) :
    3 * Real.sqrt 2 < a * x + b * y ∧ a * x + b * y ≤ 6 * Real.sqrt 2 := by

  have h3 : a + 1 / a ≥ 2 := by
    have h4 : a * (1 / a) = 1 := by field_simp
    nlinarith [sq_nonneg (a - 1)]
  
  have h6 : b + 9 / b ≥ 6 := by
    have h7 : b * (9 / b) = 9 := by
      field_simp
      <;> linarith
    nlinarith [sq_nonneg (b - 3)]
  
  have h5 : a + 1 / a = 2 := by linarith
  
  have h8 : b + 9 / b = 6 := by linarith
  
  have ha1 : a = 1 := by
    have h9 : a ^ 2 - 2 * a + 1 = 0 := by
      have h10 : a + 1 / a = 2 := h5
      field_simp at h10
      nlinarith
    have h11 : (a - 1) ^ 2 = 0 := by nlinarith
    have h12 : a - 1 = 0 := by
      rw [sq_eq_zero_iff] at h11
      exact h11
    linarith
  
  have hb1 : b = 3 := by
    have h13 : b ^ 2 - 6 * b + 9 = 0 := by
      have h14 : b + 9 / b = 6 := h8
      field_simp at h14
      nlinarith
    have h15 : (b - 3) ^ 2 = 0 := by nlinarith
    have h16 : b - 3 = 0 := by
      rw [sq_eq_zero_iff] at h15
      exact h15
    linarith
  
  have h9 : a = 1 := ha1
  have h10 : b = 3 := hb1
  
  rw [h9, h10] at h2
  
  have h12 : x ^ 2 + 3 * y ^ 2 = 18 := by linarith

  have h13 : (x + 3 * y) ^ 2 ≤ 36 * (Real.sqrt 2) ^ 2 := by
    nlinarith [sq_nonneg (x - y), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), h12, 
      mul_pos hx hy, mul_self_nonneg (x + 3 * y - 6 * Real.sqrt 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      mul_pos hx (show 0 < y by linarith [hy]), 
      mul_pos hy (show 0 < x by linarith [hx]), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
  
  have h14 : 3 * Real.sqrt 2 < a * x + b * y := by
    rw [h9, h10]
    nlinarith [sq_nonneg (x - 3 * Real.sqrt 2), sq_nonneg (y), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      h12, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num),
      mul_pos hx hy, mul_pos hx (show 0 < y by linarith [hy]), 
      mul_pos hy (show 0 < x by linarith [hx])
    ]
  
  have h15 : a * x + b * y ≤ 6 * Real.sqrt 2 := by
    rw [h9, h10]
    nlinarith [h13, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  
  constructor
  · -- Proof of the lower bound
    linarith [h14]
  · -- Proof of the upper bound
    linarith [h15]