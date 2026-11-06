import Mathlib

/- 1. Given $\alpha, \beta$ are acute angles, $\cos \alpha=\frac{\sqrt{5}}{5}, \cos \beta=$ $\frac{\sqrt{10}}{10}$. Then $\alpha+\beta=$ $\qquad$ . -/
theorem algebra_328032 (α β : ℝ) (h₁ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₂ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₃ : Real.cos α = Real.sqrt 5 / 5) (h₄ : Real.cos β = Real.sqrt 10 / 10) :
    α + β = 3 * Real.pi / 4 := by
        -- Extract the bounds for α and β from the hypotheses
        have hα1 : 0 < α := h₁.left
        have hα2 : α < Real.pi / 2 := h₁.right
        have hβ1 : 0 < β := h₂.left
        have hβ2 : β < Real.pi / 2 := h₂.right

        -- Prove that sin α > 0 since α is in (0, π/2)
        have h_sin_alpha : Real.sin α > 0 := by
            apply Real.sin_pos_of_pos_of_lt_pi
            · linarith
            · linarith [Real.pi_pos]

        -- Calculate the exact value of sin α using the Pythagorean identity
        have h_sin_alpha2 : Real.sin α = 2 * Real.sqrt 5 / 5 := by
            have h : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
            rw [h₃] at h
            have h1 : Real.sin α ^ 2 = 4 / 5 := by
                have h2 : (Real.sqrt 5 / 5 : ℝ) ^ 2 = 1 / 5 := by
                    calc
                        (Real.sqrt 5 / 5 : ℝ) ^ 2 = (Real.sqrt 5) ^ 2 / 25 := by ring
                        _ = 5 / 25 := by rw [Real.sq_sqrt]; linarith
                        _ = 1 / 5 := by norm_num
                linarith
            have h2 : Real.sin α = 2 * Real.sqrt 5 / 5 := by
                have h3 : Real.sin α = 2 * Real.sqrt 5 / 5 := by
                    have h4 : Real.sin α ^ 2 = 4 / 5 := h1
                    have h5 : Real.sin α = Real.sqrt (4 / 5) := by
                        rw [←h4]
                        field_simp [h_sin_alpha]
                    rw [h5]
                    have h6 : Real.sqrt (4 / 5) = 2 * Real.sqrt 5 / 5 := by
                        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
                        <;> ring_nf <;> norm_num
                    exact h6
                exact h3
            exact h2

        -- Prove that sin β > 0 since β is in (0, π/2)
        have h_sin_beta : Real.sin β > 0 := by
            apply Real.sin_pos_of_pos_of_lt_pi
            · linarith
            · linarith [Real.pi_pos]

        -- Calculate the exact value of sin β using the Pythagorean identity
        have h_sin_beta2 : Real.sin β = 3 * Real.sqrt 10 / 10 := by
            have h : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
            rw [h₄] at h
            have h1 : Real.sin β ^ 2 = 9 / 10 := by
                have h2 : (Real.sqrt 10 / 10 : ℝ) ^ 2 = 1 / 10 := by
                    calc
                        (Real.sqrt 10 / 10 : ℝ) ^ 2 = (Real.sqrt 10) ^ 2 / 100 := by ring
                        _ = 10 / 100 := by rw [Real.sq_sqrt]; linarith
                        _ = 1 / 10 := by norm_num
                linarith
            have h2 : Real.sin β = 3 * Real.sqrt 10 / 10 := by
                have h3 : Real.sin β = 3 * Real.sqrt 10 / 10 := by
                    have h4 : Real.sin β ^ 2 = 9 / 10 := h1
                    have h5 : Real.sin β = Real.sqrt (9 / 10) := by
                        rw [←h4]
                        field_simp [h_sin_beta]
                    rw [h5]
                    have h6 : Real.sqrt (9 / 10) = 3 * Real.sqrt 10 / 10 := by
                        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
                        <;> ring_nf <;> norm_num
                    exact h6
                exact h3
            exact h2

        -- Calculate cos(α + β) using the cosine addition formula
        have h_cos_sum : Real.cos (α + β) = -Real.sqrt 2 / 2 := by
            rw [Real.cos_add]
            rw [h₃, h₄, h_sin_alpha2, h_sin_beta2]
            have h1 : Real.sqrt 5 * Real.sqrt 10 = 5 * Real.sqrt 2 := by
                calc
                    Real.sqrt 5 * Real.sqrt 10 = Real.sqrt (5 * 10) := by rw [Real.sqrt_mul (by linarith)]
                    _ = Real.sqrt 50 := by norm_num
                    _ = Real.sqrt (5^2 * 2) := by norm_num
                    _ = Real.sqrt (5^2) * Real.sqrt 2 := by rw [Real.sqrt_mul (by linarith)]
                    _ = 5 * Real.sqrt 2 := by rw [Real.sqrt_sq (by linarith)]
            have h2 : (Real.sqrt 5 / 5 : ℝ) * (Real.sqrt 10 / 10) = Real.sqrt 2 / 10 := by
                calc
                    (Real.sqrt 5 / 5 : ℝ) * (Real.sqrt 10 / 10)
                        = (Real.sqrt 5 * Real.sqrt 10) / 50 := by ring
                    _ = 5 * Real.sqrt 2 / 50 := by rw [h1]
                    _ = Real.sqrt 2 / 10 := by ring
            have h3 : (2 * Real.sqrt 5 / 5 : ℝ) * (3 * Real.sqrt 10 / 10) = 3 * Real.sqrt 2 / 5 := by
                calc
                    (2 * Real.sqrt 5 / 5 : ℝ) * (3 * Real.sqrt 10 / 10)
                        = 6 * (Real.sqrt 5 * Real.sqrt 10) / 50 := by ring
                    _ = 6 * (5 * Real.sqrt 2) / 50 := by rw [h1]
                    _ = 30 * Real.sqrt 2 / 50 := by ring
                    _ = 3 * Real.sqrt 2 / 5 := by ring
            linarith [h2, h3]

        -- Prove that α + β = 3π/4 by showing that cos(α + β) = cos(3π/4)
        have h3 : α + β = 3 * Real.pi / 4 := by
            have h4 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
                have h4 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
                    have h1 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
                    rw [h1]
                    rw [Real.cos_pi_sub]
                    have h2 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
                    linarith
                exact h4
            have h5 : α + β = 3 * Real.pi / 4 := by
                have h6 : Real.cos (α + β) = Real.cos (3 * Real.pi / 4) := by
                    rw [h_cos_sum]
                    rw [h4]
                have h7 : α + β = 3 * Real.pi / 4 := by
                    -- Show that both angles are in [0, π] to use the injectivity of cosine
                    have h8 : α + β ∈ Set.Icc 0 Real.pi := by
                        constructor
                        · linarith
                        · linarith [Real.pi_pos]
                    have h10 : 3 * Real.pi / 4 ∈ Set.Icc 0 Real.pi := by
                        constructor
                        · linarith [Real.pi_pos]
                        · linarith [Real.pi_pos]
                    have h11 : Real.cos (α + β) = Real.cos (3 * Real.pi / 4) := h6
                    have h12 : α + β = 3 * Real.pi / 4 := by
                        apply Real.injOn_cos h8 h10 h11
                    exact h12
                exact h7
            exact h5
        exact h3
