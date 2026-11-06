import Mathlib

theorem algebra_177311 {a b c : ℝ} (h : a^2 + b^2 + c^2 = a * b + b * c + c * a) :
    a = b ∧ b = c := by

        have h1 : (a - b)^2 + (b - c)^2 + (c - a)^2 = 0 := by
            nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
 
        have h2 : (a - b)^2 = 0 := by
            linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
 
        have h3 : (b - c)^2 = 0 := by
            linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
 
        have h4 : (c - a)^2 = 0 := by 
            linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

        have h5 : a - b = 0 := by 
            rwa [sq_eq_zero_iff] at h2
        have h6 : b - c = 0 := by 
            rwa [sq_eq_zero_iff] at h3
        have h7 : a = b := by linarith
        have h8 : b = c := by linarith
        exact ⟨h7, h8⟩