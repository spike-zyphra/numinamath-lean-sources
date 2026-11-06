import Mathlib
/-Given (a^2+1)(b^2+1)=3(2ab-1). Then the value of b(1/a-a) is ?-/
theorem algebra_303790 {a b : ℝ} (ha : a ≠ 0) (h : (a ^ 2 + 1) * (b ^ 2 + 1) = 3 * (2 * a * b - 1)) :
    b * (1 / a - a) = -1 := by
    -- transform step by step
        have h1 : a^2 * b^2 + a^2 + b^2 - 6 * a * b + 4 = 0 := by
            nlinarith [h]  -- key identity
        have h2 : (a * b - 2) ^ 2 + (a - b) ^ 2 = 0 := by
            nlinarith [h1]
        have h3 : a * b - 2 = 0 := by 
            nlinarith [sq_nonneg (a * b - 2), sq_nonneg (a - b), h2]
        have h4 : a - b = 0 := by 
            nlinarith [sq_nonneg (a * b - 2), sq_nonneg (a - b), h2]
        have h5 : a = b := by linarith
        have h6 : a * b = 2 := by linarith
        have h7 : a^2 = 2 := by
            have h5' : b = a := by linarith
            rw [h5'] at h6
            nlinarith [h6]
        have h8 : b * (1 / a - a) = -1 := by 
            have h5' : b = a := by linarith
            rw [h5']
            field_simp [ha]
            nlinarith [h7]
        exact h8