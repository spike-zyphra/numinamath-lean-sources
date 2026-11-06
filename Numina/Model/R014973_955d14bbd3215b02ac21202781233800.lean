import Mathlib

theorem algebra_164600 (α β : ℝ) (h₀ : Real.sin α + Real.sin β = -27 / 65)
    (h₁ : Real.tan ((α + β) / 2) = 7 / 9) (h₂ : 5 / 2 * Real.pi < α ∧ α < 3 * Real.pi)
    (h₃ : -Real.pi / 2 < β ∧ β < 0) :
    Real.cos ((α - β) / 2) = 27 / (7 * Real.sqrt 130) := by

  have h4 : Real.sin α + Real.sin β = 2 * Real.sin ((α + β) / 2) * Real.cos ((α - β) / 2) := by
    rw [show (α : ℝ) = (α + β) / 2 + (α - β) / 2 by ring, 
        show (β : ℝ) = (α + β) / 2 - (α - β) / 2 by ring]
    rw [Real.sin_add, Real.sin_sub]
    ring

  have h8 : Real.sin ((α + β) / 2) ^ 2 + Real.cos ((α + β) / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq ((α + β) / 2)
  have h9 : Real.sin ((α + β) / 2) = 7 / 9 * Real.cos ((α + β) / 2) := by
    have htan : Real.tan ((α + β) / 2) = Real.sin ((α + β) / 2) / Real.cos ((α + β) / 2) := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan] at h₁ 
    have hcosne : Real.cos ((α + β) / 2) ≠ 0 := by 
      by_contra h 
      rw [h] at h₁ 
      norm_num at h₁ 
      all_goals linarith 
      all_goals linarith 
    field_simp [hcosne] at h₁ ⊢ 
    linarith 
    all_goals linarith

  have h11 : Real.cos ((α + β) / 2) ^ 2 = 81 / 130 := by
    have h10 : Real.sin ((α + β) / 2) ^ 2 + Real.cos ((α + β) / 2) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq ((α + β) / 2)
    rw [show Real.sin ((α + β) / 2) = 7 / 9 * Real.cos ((α + β) / 2) by linarith [h9]] at h10
    nlinarith

  have h12 : Real.pi < (α + β) / 2 ∧ (α + β) / 2 < 3 / 2 * Real.pi := by
    have h13 : 2 * Real.pi < α + β := by 
      nlinarith [h₂.1, h₃.1, Real.pi_pos]
    have h14 : α + β < 3 * Real.pi := by 
      nlinarith [h₂.2, h₃.2, Real.pi_pos]
    constructor
    · linarith 
    · linarith 
    all_goals linarith 
    all_goals linarith 
  have h15 : Real.cos ((α + β) / 2) < 0 := by
    have h16 : Real.pi < (α + β) / 2 := h12.1
    have h17 : (α + β) / 2 < 3 / 2 * Real.pi := h12.2
    have h18 : Real.cos ((α + β) / 2) < 0 := by 
      apply Real.cos_neg_of_pi_div_two_lt_of_lt 
      all_goals 
      nlinarith [Real.pi_pos, Real.pi_gt_three]
      all_goals 
      nlinarith [Real.pi_pos, Real.pi_gt_three]
    linarith

  have h20 : Real.cos ((α + β) / 2) = - Real.sqrt (81 / 130) := by
    have h21 : Real.cos ((α + β) / 2) ^ 2 = 81 / 130 := h11
    have h22 : Real.cos ((α + β) / 2) < 0 := h15
    have h23 : Real.sqrt (81 / 130 : ℝ) ≥ 0 := Real.sqrt_nonneg (81 / 130)
    have h24 : Real.sqrt (81 / 130 : ℝ) ^ 2 = 81 / 130 := by
      rw [Real.sq_sqrt]
      norm_num
    have h25 : Real.cos ((α + β) / 2) = - Real.sqrt (81 / 130 : ℝ) := by
      have h26 : Real.cos ((α + β) / 2) ^ 2 - Real.sqrt (81 / 130 : ℝ) ^ 2 = 0 := by
        linarith [h21, h24]
      have h27 : (Real.cos ((α + β) / 2) - Real.sqrt (81 / 130 : ℝ)) * (Real.cos ((α + β) / 2) + Real.sqrt (81 / 130 : ℝ)) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h27) with h28 h29
      · -- Case where Real.cos ((α + β) / 2) - Real.sqrt (81 / 130) = 0
        have h30 : Real.cos ((α + β) / 2) = Real.sqrt (81 / 130 : ℝ) := by linarith
        nlinarith [show Real.sqrt (81 / 130 : ℝ) ≥ 0 by apply Real.sqrt_nonneg, h30, Real.sqrt_nonneg (81 / 130 : ℝ)]
      · -- Case where Real.cos ((α + β) / 2) + Real.sqrt (81 / 130) = 0
        have h31 : Real.cos ((α + β) / 2) = - Real.sqrt (81 / 130 : ℝ) := by linarith
        exact h31
    exact h25

  have h28 : Real.sin ((α + β) / 2) = -7 / Real.sqrt 130 := by
    have h28' : Real.sin ((α + β) / 2) = 7 / 9 * Real.cos ((α + β) / 2) := by linarith [h9]
    rw [h28']
    rw [h20]
    have h24 : Real.sqrt (81 / 130 : ℝ) = 9 / Real.sqrt 130 := by
      have h31 : Real.sqrt (81 / 130 : ℝ) = Real.sqrt 81 / Real.sqrt 130 := by
        rw [Real.sqrt_div (by norm_num)]
        all_goals norm_num
      have h32 : Real.sqrt 81 = 9 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h31, h32]
      <;> ring_nf <;> field_simp
      <;> ring_nf <;> norm_num 
    rw [h24]
    <;> field_simp 
    <;> ring_nf <;> norm_num 
    <;> nlinarith 
    <;> positivity

  rw [h4] at h₀ 
  rw [h28] at h₀ 
  field_simp at h₀ ⊢
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (130 : ℝ) by norm_num : (0 : ℝ) < (130 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (130 : ℝ) by norm_num : (0 : ℝ) ≤ (130 : ℝ)), Real.sqrt_nonneg (130 : ℝ), Real.sqrt_nonneg (81 / 130 : ℝ)]