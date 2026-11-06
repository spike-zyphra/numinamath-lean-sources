import Mathlib

theorem algebra_306691 (x y : ℝ) (hx : x ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4)) (hy : y ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4))
    (a : ℝ) (h1 : x^3 + Real.sin x - 2 * a = 0) (h2 : 4 * y^3 + Real.sin y * Real.cos y + a = 0) :
    Real.cos (x + 2 * y) = 1 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h3 : a = (x^3 + Real.sin x) / 2 := by
    linarith 
  have h4 : 4 * y^3 + Real.sin y * Real.cos y + (x^3 + Real.sin x) / 2 = 0 := by 
    rw [h3] at h2
    linarith [h2]
  have h5 : x + 2 * y = 0 := by 
    -- From h6, to show x = -2y
    have eq1 : x ^ 3 + Real.sin x + 8 * y^3 + 2 * Real.sin y * Real.cos y = 0 := by
      nlinarith [h4]
    -- From eq1, to show that x = -2y.
    have h_eq : x = -2 * y := by
      have eq5 : x^3 + Real.sin x = -8 * y^3 - 2 * Real.sin y * Real.cos y := by
          linarith [eq1]
      -- Now to show x = -2*y
      have eq5' : x^3 + Real.sin x = ((-2 * y) ^ 3 + Real.sin (-2 * y)) := by 
          have eq5'' : (-2 * y) ^ 3 + Real.sin (-2 * y) =  -8 * y^3 - 2 * Real.sin y * Real.cos y := by 
            have h13 : Real.sin (-2 * y) = - Real.sin (2 * y) := by 
              rw [show -2 * y = - (2 * y) by ring]
              rw [Real.sin_neg]
              <;> ring_nf <;> simp [Real.sin_two_mul]
              <;> ring_nf
            have h10 : (-2 * y) ^ 3 = -8 * y^3 := by ring 
            rw [h13, h10]
            have h11 : Real.sin (2 * y) = 2 * Real.sin y * Real.cos y := by 
              rw [Real.sin_two_mul]
            rw [h11] at h13
            all_goals linarith
          linarith [eq5, eq5'']
      have h_eq_2 : x = -2 * y := by
        -- Show using bounds
        have h91 : x ≤ Real.pi / 4 := hx2
        have h92 : -Real.pi / 4 ≤ x := hx1
        have h93 : y ≤ Real.pi / 4 := hy2
        have h94 : -Real.pi / 4 ≤ y := hy1
        -- Goal: x = -2*y
        -- Function is strictly increasing: f(x) = x^3 + sinx
        by_cases h10 : x < -2 * y 
        · -- Then x^3 + sin x < (-2y)^3 + sin(-2y), contradiction
          have h8 : Real.sin x < Real.sin (-2 * y) := by
            apply Real.sin_lt_sin_of_lt_of_le_pi_div_two 
            all_goals 
              nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_le_one x, Real.sin_le_one y, Real.sin_le_one (-2 * y), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq (-2 * y)]
          have h62 : x^3 < (-2 * y)^3 := by
            nlinarith [sq_nonneg (x + 2 * y), sq_nonneg (x - (-2 * y)), sq_nonneg (x^2 -4 * y^2), sq_nonneg (x^3 +8*y^3), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq (-2 * y), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y), Real.sin_sq_add_cos_sq (-2 * y)]
          have h63 : x^3 + Real.sin x < ((-2 * y)^3 + Real.sin (-2 * y) ) := by 
              nlinarith [Real.sin_le_one (-2 * y), Real.sin_le_one x, Real.sin_le_one y, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq (-2 * y)]
          linarith [h63, eq5']
        · -- Now either x >= -2y
          by_cases h11 : x > -2 * y
          · -- Show contradiction, x^3 + sinx > (-2y)^3 + sin(-2y)
            have h8 : Real.sin x > Real.sin (-2 * y) := by
              apply Real.sin_lt_sin_of_lt_of_le_pi_div_two 
              all_goals 
                nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_le_one x, Real.sin_le_one y, Real.sin_le_one (-2 * y), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq (-2 * y)]
            have h62 : x^3 > (-2 * y)^3 := by
              nlinarith [sq_nonneg (x + 2 * y), sq_nonneg (x - (-2 * y)), sq_nonneg (x^2 -4 * y^2), sq_nonneg (x^3 +8*y^3), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq (-2 * y), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y), Real.sin_sq_add_cos_sq (-2 * y)]
            have h63 : x^3 + Real.sin x > ((-2 * y)^3 + Real.sin (-2 * y) ) := by 
              nlinarith [Real.sin_le_one (-2 * y), Real.sin_le_one x, Real.sin_le_one y, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq (-2 * y)]
            linarith [h63, eq5']
          · -- Now x = -2y
            have h12 : x = -2 * y := by linarith
            linarith
      linarith 
    linarith 
  have h6 : Real.cos (x + 2 * y) = 1 := by 
    rw [show x + 2 * y = (0 : ℝ) by linarith [h5]]
    norm_num 
  exact h6