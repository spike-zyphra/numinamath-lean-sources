import Mathlib

theorem algebra_166413 {x y z : ℝ} (h₀ : Real.sqrt (x + y) + Real.sqrt (y + z) = 3)
    (h₁ : Real.sqrt (y + z) + Real.sqrt (z + x) = 5) (h₂ : Real.sqrt (z + x) + Real.sqrt (x + y) = 4) :
    x = 3 ∧ y = -2 ∧ z = 6 := by

  have h3 : Real.sqrt (x + y) = 1 := by 
    nlinarith [h₀, h₁, h₂, 
      Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x),
      sq_nonneg (Real.sqrt (x + y) - 1), sq_nonneg (Real.sqrt (y + z) - 2), sq_nonneg (Real.sqrt (z + x) - 3)
    ]

  have h4 : Real.sqrt (y + z) = 2 := by 
    nlinarith [h₀, h3, 
      Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x)
    ]

  have h5 : Real.sqrt (z + x) = 3 := by 
    nlinarith [h₁, h4, 
      Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x)
    ]

  have h6 : x + y ≥ 0 := by
    by_contra h
    push_neg at h
    have h8 : Real.sqrt (x + y) = 0 := by
      apply Real.sqrt_eq_zero'.mpr
      linarith
    linarith

  have h7 : y + z ≥ 0 := by
    by_contra h
    push_neg at h
    have h8 : Real.sqrt (y + z) = 0 := by
      apply Real.sqrt_eq_zero'.mpr
      linarith
    linarith

  have h8 : z + x ≥ 0 := by
    by_contra h
    push_neg at h
    have h9 : Real.sqrt (z + x) = 0 := by
      apply Real.sqrt_eq_zero'.mpr
      linarith
    linarith

  have h9 : x + y = 1 := by 
    calc 
      x + y = (Real.sqrt (x + y)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = (1 : ℝ) ^ 2 := by
        rw [h3]
      _ = (1 : ℝ) := by 
        norm_num

  have h10 : y + z = 4 := by
    calc 
      y + z = (Real.sqrt (y + z)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = (2 : ℝ) ^ 2 := by
        rw [h4]
      _ = (4 : ℝ) := by 
        norm_num

  have h11 : z + x = 9 := by 
    calc 
      z + x = (Real.sqrt (z + x)) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith
      _ = (3 : ℝ) ^ 2 := by 
        rw [h5]
      _ = (9 : ℝ) := by 
        norm_num

  have hx : x = 3 := by
    nlinarith [h9, h10, h11]

  have hy : y = -2 := by
    nlinarith [h9, hx]

  have hz : z = 6 := by
    nlinarith [h11, hx]

  exact ⟨hx, hy, hz⟩