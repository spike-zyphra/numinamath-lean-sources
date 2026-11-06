import Mathlib

theorem algebra_251689 (α β : ℝ) (h₀ : 0 < α ∧ α < Real.pi / 2) (h₁ : 0 < β ∧ β < Real.pi / 2) :
    (Real.sin α ^ 2 + Real.sin β ^ 2 = Real.sin (α + β) ^ 2) ↔ (α + β = Real.pi / 2) := by 
  constructor
  · -- Assume $\sin^2 \alpha + \sin^2 \beta = \sin^2(\alpha + \beta)$, prove $\alpha + \beta = \frac{\pi}{2}$
    intro h
    have h2 : 0 < α := h₀.1
    have h3 : α < Real.pi / 2 := h₀.2
    have h4 : 0 < β := h₁.1
    have h5 : β < Real.pi / 2 := h₁.2
    have h6 : Real.sin α > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_gt_three, h3]
    have h7 : Real.sin β > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_gt_three, h5]
    have h8 : Real.cos α > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith [Real.pi_gt_three, h3]
    have h9 : Real.cos β > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith [Real.pi_gt_three, h5]
    have h10 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
      rw [Real.sin_add]
    rw [h10] at h
    have h11 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
    have h12 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
    have h17 : Real.sin α * Real.sin β = Real.cos α * Real.cos β := by
      have eq1 : Real.sin α ^ 2 + Real.sin β ^ 2 = (Real.sin α * Real.cos β + Real.cos α * Real.sin β) ^ 2 := h
      have eq2 : (Real.sin α * Real.cos β + Real.cos α * Real.sin β) ^ 2 =
          Real.sin α ^ 2 * Real.cos β ^ 2 + Real.cos α ^ 2 * Real.sin β ^ 2 + 2 * (Real.sin α * Real.cos β * Real.cos α * Real.sin β) := by ring
      rw [eq2] at eq1
      have eq3 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by linarith [h11]
      have eq4 : Real.cos β ^ 2 = 1 - Real.sin β ^ 2 := by linarith [h12]
      -- Now we need positivity for Real.sin α > 0 and Real.sin β > 0 to divide
      have hsinα : Real.sin α > 0 := h6
      have hsinβ : Real.sin β > 0 := h7
      -- Now we'll need to show that $eq1$ and $\eq3, \eq4$
      have eq5 : Real.sin α ^ 2 + Real.sin β ^ 2 = Real.sin α ^ 2 * Real.cos β ^ 2 + Real.cos α ^ 2 * Real.sin β ^ 2 + 2 * (Real.sin α * Real.cos β * Real.cos α * Real.sin β) := by linarith [eq1]
      rw [eq3, eq4] at eq5
      -- Multiply through and simplify.
      have eq6 : (Real.sin α * Real.sin β - Real.cos α * Real.cos β) = 0 := by
        nlinarith [sq_pos_of_pos h6, sq_pos_of_pos h7, sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, mul_pos h6 h7, sq_nonneg (Real.sin α * Real.sin β), sq_nonneg (Real.cos α * Real.cos β)]
      linarith
    have h18 : Real.cos (α + β) = 0 := by
      have h19 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by
        rw [Real.cos_add]
      rw [h19]
      nlinarith [h17]
    have h18' : α + β > 0 := by linarith [h₀.1, h₁.1]
    have h19 : α + β < Real.pi := by
      linarith [h₀.2, h₁.2, Real.pi_gt_three]
    have h20 : α + β = Real.pi / 2 := by
      by_cases h5 : α + β < Real.pi / 2
      · -- Assume α + β < Real.pi / 2
        have h24 : Real.cos (α + β) > 0 := by
          apply Real.cos_pos_of_mem_Ioo
          constructor
          · -- Show -π/2 < α + β
            linarith
          · -- Show α + β < π/2
            linarith
        linarith -- Contradicts with Real.cos (α + β) = 0
      by_cases h6 : α + β > Real.pi / 2
      · -- Assume α + β > Real.pi / 2
        have h25 : Real.cos (α + β) < 0 := by
          apply Real.cos_neg_of_pi_div_two_lt_of_lt
          all_goals linarith
        linarith -- Contradicts with Real.cos (α + β) = 0
      linarith [show Real.pi / 2 ≤ α + β by linarith, show α + β ≤ Real.pi / 2 by linarith]
    assumption
  · -- Assume α + β = Real.pi / 2, prove $\sin^2 \alpha + \sin^2 \beta = \sin^2(\alpha + \beta)$
    intro h
    have h2 : 0 < α := h₀.1
    have h3 : α < Real.pi / 2 := h₀.2
    have h4 : 0 < β := h₁.1
    have h5 : β < Real.pi / 2 := h₁.2
    have h6 : Real.sin α > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_gt_three, h3]
    have h7 : Real.sin β > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_gt_three, h5]
    have h9 : β = Real.pi / 2 - α := by 
      linarith
    have h10 : Real.sin β = Real.cos α := by
      rw [h9]
      have h11 : Real.sin (Real.pi / 2 - α) = Real.cos α := by
        rw [Real.sin_pi_div_two_sub]
      linarith
    have h13 : Real.sin (α + β) = 1 := by
      have h14 : α + β = Real.pi / 2 := h
      rw [h14]
      have h15 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      linarith
    rw [h13]
    have h17 : Real.sin α ^ 2 + Real.sin β ^ 2 = 1 := by
      rw [h10]
      have h19 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      linarith [h19]
    linarith [h17]