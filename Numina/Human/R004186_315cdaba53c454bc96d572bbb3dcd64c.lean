import Mathlib

open Real

/- Let the numbers $\alpha, \beta$ satisfy $0<\alpha<\beta<\pi / 2$ and let $\gamma$ and $\delta$ be the numbers defined by the conditions:

(i) $0<\gamma<\pi / 2$, and $\tan \gamma$ is the arithmetic mean of $\tan \alpha$ and $\tan \beta$;

(ii) $0<\delta<\pi / 2$, and $\frac{1}{\cos \delta}$ is the arithmetic mean of $\frac{1}{\cos \alpha}$ and $\frac{1}{\cos \beta}$.

Prove that $\gamma<\delta$. -/

theorem algebra_241161 {α β γ δ : ℝ}
  (h₀ : 0 < α ∧ α < β ∧ β < π / 2)
  (h₁ : 0 < γ ∧ γ < π / 2 ∧ tan γ = (tan α + tan β) / 2)
  (h₂ : 0 < δ ∧ δ < π / 2 ∧ 1 / cos δ = (1 / cos α + 1 / cos β) / 2) :
  γ < δ := by

  let f : ℝ → ℝ := fun x => √(1 + x ^ 2)

  have hf_convex : StrictConvexOn ℝ Set.univ f := by
    apply strictConvexOn_of_deriv2_pos convex_univ
    · -- f is continuous
      apply Continuous.continuousOn
      apply Continuous.sqrt
      apply Continuous.add
      · exact continuous_const
      · exact continuous_pow 2
    · -- Second derivative f''(x) = 1/(1+x²)^(3/2) > 0
      intro x hx
      -- For f(x) = √(1 + x²), the complete differentiation process:
      --
      -- Step 1: First derivative
      -- f'(x) = d/dx √(1 + x²) = x / √(1 + x²)
      --
      -- Step 2: Second derivative (using quotient rule)
      -- f''(x) = d/dx [x / √(1 + x²)] = 1 / (1 + x²)^(3/2)
      --
      -- Step 3: Prove f''(x) > 0
      -- Since 1 > 0 and (1 + x²)^(3/2) > 0 for all real x,
      -- therefore f''(x) = 1 / (1 + x²)^(3/2) > 0

      -- This calculation involves multiple differential theorems and algebraic simplification
      -- This is a standard result in calculus

      -- First prove 1 + x^2 > 0
      have h_pos : 0 < 1 + x^2 := by
        apply add_pos_of_pos_of_nonneg
        · norm_num
        · exact sq_nonneg x

      -- Then prove the function is differentiable
      have h_diff : DifferentiableAt ℝ (fun y => 1 + y^2) x := by
        apply DifferentiableAt.add
        · exact differentiableAt_const 1
        · exact differentiableAt_pow 2

      -- Use known result: for g(x) = √(1 + x²), second derivative is 1/(1+x²)^(3/2)
      have h_formula : (deriv^[2] f) x = 1 / (1 + x^2)^(3/2 : ℝ) := by
        simp [f]

        -- Step 1: Compute first derivative f'(x) = x / √(1 + x²)
        have h_deriv1 : deriv (fun y => √(1 + y^2)) x = x / √(1 + x^2) := by
          rw [deriv_sqrt h_diff h_pos.ne']
          simp [deriv_add, deriv_const, deriv_pow, deriv_id'']
          ring

        -- Step 2: Compute second derivative
        have h_deriv2_eq : deriv (deriv (fun y => √(1 + y^2))) x =
                          deriv (fun y => y / √(1 + y^2)) x := by
          congr 1
          ext y
          rw [deriv_sqrt]
          · simp [deriv_add, deriv_const, deriv_pow, deriv_id'']
            ring
          · apply DifferentiableAt.add
            · exact differentiableAt_const 1
            · exact differentiableAt_pow 2
          · apply ne_of_gt
            apply add_pos_of_pos_of_nonneg; norm_num; exact sq_nonneg y

        rw [h_deriv2_eq]

        -- Compute d/dx [x / √(1 + x²)] using quotient rule
        rw [deriv_div]
        · -- Numerator: deriv(x) * √(1 + x²) - x * deriv(√(1 + x²))
          simp [deriv_id'']
          rw [deriv_sqrt h_diff h_pos.ne']
          simp [deriv_add, deriv_const, deriv_pow, deriv_id'']
          -- Simplify: √(1 + x²) - x * (x / √(1 + x²)) = √(1 + x²) - x² / √(1 + x²)
          field_simp [Real.sqrt_ne_zero'.mpr h_pos]
          ring_nf
          rw [sq_sqrt (by positivity)]
          ring_nf
          have : x ^ 2 * √(1 + x ^ 2) * 2 + √(1 + x ^ 2) * 2 = (1 + x ^ 2) * √(1 + x ^ 2) * 2 := by
            ring_nf
          rw [this]

          rw [(show (3:ℝ)/2 = 1 + 1/2 by norm_num)]
          rw [Real.rpow_add h_pos]
          rw [rpow_one]
          congr 2
          rw [← Real.sqrt_eq_rpow]

        · exact differentiableAt_id'
        · apply DifferentiableAt.sqrt h_diff h_pos.ne'
        · exact Real.sqrt_ne_zero'.mpr h_pos

      -- Finally prove this expression is positive
      rw [h_formula]
      apply div_pos
      · norm_num
      · apply Real.rpow_pos_of_pos h_pos

  -- Apply strict Jensen's inequality
  have h_jensen : f ((tan α + tan β) / 2) < (f (tan α) + f (tan β)) / 2 := by
    -- Use the modus ponens direction of strictConvexOn_iff_div
    have h_strict := (strictConvexOn_iff_div).mp hf_convex
    have h_tan_ne : tan α ≠ tan β := by
      exact ne_of_lt (tan_lt_tan_of_lt_of_lt_pi_div_two
        (by linarith [h₀.1, h₀.2.2])
        (by linarith [h₀.1, h₀.2.1, h₀.2.2])
        h₀.2.1)

    -- For a = b = 1, we have a/(a+b) = b/(a+b) = 1/2
    have h_apply := h_strict.2 (Set.mem_univ _) (Set.mem_univ _) h_tan_ne
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)

    -- Convert expressions to match
    convert h_apply using 1
    · simp [smul_eq_mul]
      ring_nf
    · simp [smul_eq_mul]
      ring

  -- Convert f function to secant function form
  have h_sec_γ : f (tan γ) = 1 / cos γ := by
    rw [← inv_sqrt_one_add_tan_sq (show 0 < cos γ by
      apply cos_pos_of_mem_Ioo
      exact ⟨by linarith [h₁.1], h₁.2.1⟩)]
    simp [f]

  have h_sec_α : f (tan α) = 1 / cos α := by
    rw [← inv_sqrt_one_add_tan_sq (show 0 < cos α by
      apply cos_pos_of_mem_Ioo
      exact ⟨by linarith [h₀.1], by linarith [h₀.2.2]⟩)]
    simp [f]

  have h_sec_β : f (tan β) = 1 / cos β := by
    rw [← inv_sqrt_one_add_tan_sq (show 0 < cos β by
      apply cos_pos_of_mem_Ioo
      exact ⟨by linarith [h₀.1, h₀.2.1], by linarith [h₀.2.2]⟩)]
    simp [f]

  -- By condition h₁: tan γ = (tan α + tan β) / 2
  rw [← h₁.2.2] at h_jensen

  -- Convert inequality to secant form
  rw [h_sec_γ, h_sec_α, h_sec_β] at h_jensen

  -- By condition h₂: (1/cos α + 1/cos β) / 2 = 1/cos δ
  have h_rhs : (1 / cos α + 1 / cos β) / 2 = 1 / cos δ := by
    exact h₂.2.2.symm

  rw [h_rhs] at h_jensen

  -- Now we have 1/cos γ < 1/cos δ
  -- On (0, π/2), cos is strictly decreasing, 1/cos is strictly increasing, so γ < δ
  have h_cos_pos_γ : 0 < cos γ := by
    apply cos_pos_of_mem_Ioo
    exact ⟨by linarith [h₁.1], h₁.2.1⟩
  have h_cos_pos_δ : 0 < cos δ := by
    apply cos_pos_of_mem_Ioo
    exact ⟨by linarith [h₂.1], h₂.2.1⟩

  -- From 1/cos γ < 1/cos δ and both cosines positive, get cos δ < cos γ
  have h_cos_rev : cos δ < cos γ := by
    rwa [div_lt_div_iff₀ h_cos_pos_γ h_cos_pos_δ, one_mul, one_mul] at h_jensen

  -- On (0, π/2) cos is strictly decreasing, so cos δ < cos γ implies γ < δ
  -- Since cos is monotone decreasing on (0, π/2), cos δ < cos γ means γ < δ
  have h_γ_in : γ ∈ Set.Ioo 0 (π / 2) := ⟨h₁.1, h₁.2.1⟩
  have h_δ_in : δ ∈ Set.Ioo 0 (π / 2) := ⟨h₂.1, h₂.2.1⟩
  -- Use proof by contradiction: if δ ≤ γ, then cos γ ≤ cos δ, contradiction
  by_contra h_not_lt
  push_neg at h_not_lt
  have h_cos_ge : cos γ ≤ cos δ := by
    apply cos_le_cos_of_nonneg_of_le_pi
    · exact le_of_lt h_δ_in.1
    · exact le_of_lt (h_γ_in.2.trans (by linarith : π / 2 < π))
    · exact h_not_lt
  linarith [h_cos_rev]
