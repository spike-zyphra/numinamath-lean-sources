import Mathlib

theorem algebra_320333 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.sqrt a * (Real.sqrt a + 2 * (b ^ ((1 : ℝ) / 3))) =
      (b ^ ((1 : ℝ) / 3)) * (Real.sqrt a + 6 * (b ^ ((1 : ℝ) / 3)))) :
    (2 * a ^ 4 + a ^ 3 * b - 128 * a * b ^ 2 - 64 * b ^ 3 + b ^ 4) /
    (a ^ 4 + 2 * a ^ 3 * b - 64 * a * b ^ 2 - 128 * b ^ 3 + 2 * b ^ 4) = 1 / 2 := by

  have ha2 : 0 < Real.sqrt a := by
    positivity
  have hb2 : 0 < b ^ ((1 : ℝ) / 3) := by
    positivity

  have h_eq : Real.sqrt a = 2 * (b ^ ((1 : ℝ) / 3)) := by
    nlinarith [sq_nonneg (Real.sqrt a - 2 * (b ^ ((1 : ℝ) / 3)) ), 
      sq_nonneg (Real.sqrt a + 2 * (b ^ ((1 : ℝ) / 3)) ), 
      sq_nonneg (b ^ ((1 : ℝ) / 3) ) 
      ]

  have h1 : a ^ 3 = 64 * b ^ 2 := by
    have h2 : Real.sqrt a = 2 * (b ^ ((1 : ℝ) / 3)) := h_eq
    have h3 : (Real.sqrt a) ^ 2 = a := by
      rw [Real.sq_sqrt]
      linarith
    have h4 : (b ^ ((1 : ℝ) / 3)) ^ 3 = b := by
      have h5 : ((b ^ ((1 : ℝ) / 3)) ^ 3) = (b ^ ((1 : ℝ) / 3 * 3)) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        all_goals norm_num
        all_goals linarith
      have h6 : (b ^ ((1 : ℝ) / 3 * 3)) = b := by
        have h7 : (1 : ℝ) / 3 * 3 = 1 := by ring
        rw [h7]
        simp
      rw [h5, h6]
    
    calc
      a ^ 3 = ((Real.sqrt a) ^ 2) ^ 3 := by rw [h3]
      _ = (Real.sqrt a) ^ 6 := by ring
      _ = (2 * (b ^ ((1 : ℝ) / 3)))^6 := by rw [h2]
      _ = 64 * ((b ^ ((1 : ℝ) / 3)) ^ 6) := by ring
      _ = 64 * ((b ^ ((1 : ℝ) / 3))^3)^2 := by ring
      _ = 64 * (b)^2 := by rw [h4]

  have num_eq : 2 * a ^ 4 + a ^ 3 * b - 128 * a * b ^ 2 - 64 * b ^ 3 + b ^ 4 = b ^ 4 := by
    have ha4 : a^4 = a * a^3 := by ring
    rw [ha4]
    have ha3 : a^3 = 64 * b^2 := h1
    rw [ha3]
    nlinarith [sq_nonneg (a - 8 * b), sq_nonneg (b), sq_nonneg (a + 8 * b)]

  have den_eq : a ^ 4 + 2 * a ^ 3 * b - 64 * a * b ^ 2 - 128 * b ^ 3 + 2 * b ^ 4 = 2 * b ^ 4 := by
    have ha4 : a^4 = a * a^3 := by ring
    rw [ha4]
    have ha3 : a^3 = 64 * b^2 := h1
    rw [ha3]
    nlinarith [sq_nonneg (a - 8 * b), sq_nonneg (b), sq_nonneg (a + 8 * b)]

  rw [num_eq, den_eq]
  have hb4 : b^4 ≠ 0 := by
    positivity

  field_simp [hb4]
  <;> nlinarith