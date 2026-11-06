import Mathlib

theorem algebra_240176 {f : ℝ → ℝ} (hf : f = fun x => (x - 1) / (x + 1)) (a b : ℝ)
    (ha : f (a ^ 2) * f a = 0.72) (hb : f (b ^ 2) * f b = 0.72) (h : a > b) :
    19 * a + 7 * b = 134 := by 
        have f_eq : ∀ x, f x = (x - 1) / (x + 1) := by
            intro x
            rw [hf]
        have eq1 : f (a ^ 2) * f a = (0.72 : ℝ) := ha
        have eq2 : f (b ^ 2) * f b = (0.72 : ℝ) := hb
        -- Substitute in eq1
        have h0 : ( ( (a ^ 2 - 1) / (a ^ 2 + 1) ) * ( (a - 1) / (a + 1) ) ) = (0.72 : ℝ) := by
            rw [show f (a ^ 2) = (a ^ 2 - 1) / (a ^ 2 + 1) by rw [f_eq] ] at eq1
            rw [show f a = (a - 1) / (a + 1) by rw [f_eq] ] at eq1
            linarith
        -- Substitute in eq2
        have h1 : ( ( (b ^ 2 - 1) / (b ^ 2 + 1) ) * ( (b - 1) / (b + 1) ) ) = (0.72 : ℝ) := by
            rw [show f (b ^ 2) = (b ^ 2 - 1) / (b ^ 2 + 1) by rw [f_eq] ] at eq2
            rw [show f b = (b - 1) / (b + 1) by rw [f_eq] ] at eq2
            linarith
        have ha1 : ( (a - 1)^2 ) = (0.72 : ℝ) * (a^2 + 1 ) := by
            have h5 : (a + 1) ≠ 0 := by
                by_contra h_eq
                have h_eq' : a = -1 := by linarith
                rw [h_eq'] at h0
                norm_num [show (a ^ 2 - 1 : ℝ) = 0 by nlinarith, show (a ^ 2 + 1 : ℝ) = 2 by nlinarith, show (a - 1 : ℝ) = -2 by linarith, show (a + 1 : ℝ) = 0 by nlinarith] at h0 ⊢
                all_goals linarith
                all_goals nlinarith
                all_goals nlinarith
            have h6 : (a ^ 2 + 1 : ℝ) ≠ 0 := by nlinarith
            have h7 : ( ( (a ^ 2 - 1) / (a ^ 2 + 1) ) * ( (a - 1) / (a + 1) ) ) = ( (a - 1)^2 ) / (a ^ 2 + 1 ) := by
                field_simp [h6, h5, sq_pos_of_ne_zero (show (a + 1 : ℝ) ≠ 0 by assumption), sq_nonneg (a + 1), sq_nonneg (a ^ 2 + 1)]
                <;> ring_nf
                <;> field_simp [h6, h5]
                <;> nlinarith
            rw [h7] at h0
            field_simp [h6, h5] at h0 ⊢
            <;> ring_nf at h0 ⊢
            <;> nlinarith 
        have hb1 : ( (b - 1)^2 ) = (0.72 : ℝ) * (b^2 + 1 ) := by
            have h5 : (b + 1) ≠ 0 := by
                by_contra h_eq
                have h_eq' : b = -1 := by linarith
                rw [h_eq'] at h1
                norm_num [show (b ^ 2 - 1 : ℝ) = 0 by nlinarith, show (b ^ 2 + 1 : ℝ) = 2 by nlinarith, show (b - 1 : ℝ) = -2 by linarith, show (b + 1 : ℝ) = 0 by nlinarith] at h1 ⊢
                all_goals linarith
                all_goals nlinarith
            have h6 : (b ^ 2 + 1 : ℝ) ≠ 0 := by nlinarith
            have h7 : ( ( (b ^ 2 - 1) / (b ^ 2 + 1) ) * ( (b - 1) / (b + 1) ) ) = ( (b - 1)^2 ) / (b ^ 2 + 1 ) := by
                field_simp [h6, h5, sq_pos_of_ne_zero (show (b + 1 : ℝ) ≠ 0 by assumption), sq_nonneg (b + 1), sq_nonneg (b ^ 2 + 1)]
                <;> ring_nf
                <;> field_simp [h6, h5]
                <;> nlinarith
            rw [h7] at h1
            field_simp [h6, h5] at h1 ⊢
            <;> ring_nf at h1 ⊢
            <;> nlinarith 
        have eq3 : ( 7 * a^2 - 50 * a + 7 ) = 0 := by
            ring_nf at ha1 ⊢
            nlinarith
        have eq4 : ( 7 * b^2 - 50 * b + 7 ) = 0 := by
            ring_nf at hb1 ⊢
            nlinarith
        have h5 : (a - 7) * (a - 1/7) = 0 := by
            nlinarith
        have h6 : (b - 7) * (b - 1/7) = 0 := by
            nlinarith
        cases' (mul_eq_zero.mp h5) with h7 h1 
        · -- a = 7
            have ha1 : a = (7 : ℝ) := by linarith
            cases' (mul_eq_zero.mp h6) with h8 h2 
            · -- b = 7
                have hb1 : b = (7 : ℝ) := by linarith
                linarith
            · -- b = 1/7 
                have hb2 : b = (1/7 : ℝ) := by linarith
                nlinarith
        · -- a = 1/7
            have ha2 : a = (1/7 : ℝ) := by linarith
            cases' (mul_eq_zero.mp h6) with h8 h2 
            · -- b = 7
                have hb1 : b = (7 : ℝ) := by linarith
                nlinarith
            · -- b = 1/7 
                have hb2 : b = (1/7 : ℝ) := by linarith
                linarith