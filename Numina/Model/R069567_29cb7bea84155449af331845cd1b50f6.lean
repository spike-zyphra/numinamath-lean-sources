import Mathlib

theorem algebra_314877 (x : Fin 5 → ℝ)
    (h₁ : 2 * x 0 + x 1 + x 2 + x 3 + x 4 = 6)
    (h₂ : x 0 + 2 * x 1 + x 2 + x 3 + x 4 = 12)
    (h₃ : x 0 + x 1 + 2 * x 2 + x 3 + x 4 = 24)
    (h₄ : x 0 + x 1 + x 2 + 2 * x 3 + x 4 = 48)
    (h₅ : x 0 + x 1 + x 2 + x 3 + 2 * x 4 = 96) :
    3 * x 3 + 2 * x 4 = 181 := by 
        have eq6 : x 1 = x 0 + 6 := by 
            linarith 
        have eq7 : x 2 = x 1 + 12 := by 
            linarith 
        have eq8 : x 3 = x 2 + 24 := by 
            linarith 
        have eq9 : x 4 = x 3 + 48 := by 
            linarith 
        have h_x0 : x 0 = -25 := by
            have eq2 : x 2 = x 0 + 18 := by 
                linarith [eq6, eq7]
            have eq3 : x 3 = x 0 + 42 := by 
                linarith [eq8, eq2]
            have eq4 : x 4 = x 0 + 90 := by 
                linarith [eq9, eq3]
            linarith [h₁, eq6, eq2, eq3, eq4]
        have hx1 : x 1 = -19 := by 
            rw [h_x0] at eq6 
            linarith 
        have hx2 : x 2 = -7 := by 
            rw [hx1] at eq7 
            linarith 
        have hx3 : x 3 = 17 := by 
            rw [hx2] at eq8 
            linarith 
        have hx4 : x 4 = 65 := by 
            rw [hx3] at eq9 
            linarith 
        rw [hx3, hx4]
        all_goals norm_num