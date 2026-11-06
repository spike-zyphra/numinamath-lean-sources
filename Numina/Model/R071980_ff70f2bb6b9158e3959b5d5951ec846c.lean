import Mathlib

theorem algebra_249008 (x y : ℝ) (h : Real.cos x + Real.cos y = 1) :
    Real.sin x - Real.sin y ∈ Set.Icc (-Real.sqrt 3) (Real.sqrt 3) := by 
        have h1 : (Real.sin x - Real.sin y) ^ 2 ≤ 3 := by
            nlinarith [sq_nonneg (Real.sin x + Real.sin y), 
                      sq_nonneg (Real.cos x - Real.cos y), 
                      Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, 
                      Real.cos_sq_add_sin_sq x, Real.cos_sq_add_sin_sq y, 
                      Real.cos_add x y, Real.sin_add x y, 
                      Real.sin_sq_le_one x, Real.sin_sq_le_one y, 
                      Real.cos_sq_le_one x, Real.cos_sq_le_one y 
                     ]
        have h2 : -Real.sqrt 3 ≤ Real.sin x - Real.sin y := by
            have h4 : (Real.sin x - Real.sin y) ^ 2 ≤ 3 := h1
            have h5 : -Real.sqrt 3 ≤ Real.sin x - Real.sin y := by 
                nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
                          Real.sqrt_nonneg 3, h4
                         ]
            exact h5
        have h3 : Real.sin x - Real.sin y ≤ Real.sqrt 3 := by
            have h7 : (Real.sin x - Real.sin y) ^ 2 ≤ 3 := h1
            have h8 : Real.sin x - Real.sin y ≤ Real.sqrt 3 := by 
                nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
                          Real.sqrt_nonneg 3, h7
                         ]
            exact h8
        exact ⟨h2, h3⟩