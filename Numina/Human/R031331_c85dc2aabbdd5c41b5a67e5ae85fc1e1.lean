import Mathlib

theorem algebra_179067 (α : ℝ) (n : ℝ) (h : Real.sin α - Real.cos α = n) :
Real.sin α ^ 3 - Real.cos α ^ 3 = (3 * n - n ^ 3) / 2 := by
      have h1 : Real.sin α ^ 3 - Real.cos α ^ 3 = (Real.sin α - Real.cos α) * (Real.sin α ^ 2 + Real.sin α * Real.cos α + Real.cos α ^ 2) := by 
          ring
      rw [h] at h1
      have h2 : Real.sin α ^ 2 + Real.sin α * Real.cos α + Real.cos α ^ 2 = (3 - n ^ 2) / 2 := by
          have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := by
              exact Real.sin_sq_add_cos_sq α
          have h4 : Real.sin α * Real.cos α = (1 - n ^ 2) / 2 := by
              have h4 : (Real.sin α - Real.cos α) ^ 2 = n ^ 2 := by 
                  rw [h]
              have h5 : (Real.sin α - Real.cos α) ^ 2 = Real.sin α ^ 2 - 2 * Real.sin α * Real.cos α + Real.cos α ^ 2 := by ring
              rw [h5] at h4
              have h6 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := by 
                  exact Real.sin_sq_add_cos_sq α
              linarith
          linarith
      rw [h1, h2]
      ring