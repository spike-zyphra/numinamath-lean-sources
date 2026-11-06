import Mathlib

theorem algebra_183740 (α β : ℝ) (h₁ : α ∈ Set.Ioo (3 * Real.pi / 4) Real.pi)
    (h₂ : β ∈ Set.Ioo (3 * Real.pi / 4) Real.pi) (h₃ : Real.sin (α + β) = -3 / 5)
    (h₄ : Real.sin (β - Real.pi / 4) = 12 / 13) :
    Real.cos (α + Real.pi / 4) = -56 / 65 := by
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h₅ : Real.cos (α + β) = 4 / 5 := by
    have h₆ : Real.cos (α + β) ^ 2 + Real.sin (α + β) ^ 2 = 1 := Real.cos_sq_add_sin_sq (α + β)
    rw [h₃] at h₆
    have h₇ : Real.cos (α + β) ^ 2 = 16 / 25 := by linarith
    have h₈ : Real.cos (α + β) > 0 := by
      have h₇₁ : α + β > 3 * Real.pi / 2 := by
        nlinarith [Real.pi_pos, h₁₁, h₁₂, h₂₁, h₂₂]
      have h₇₂ : α + β < 2 * Real.pi := by
        nlinarith [Real.pi_pos, h₁₁, h₁₂, h₂₁, h₂₂]
      have h₇₃ : Real.cos (α + β) > 0 := by
        have h₇₄ : α + β ∈ Set.Icc (3 * Real.pi / 2) (2 * Real.pi) := by
          constructor <;> nlinarith [Real.pi_pos, h₇₁, h₇₂]
        have h₇₅ : α + β - 2 * Real.pi ∈ Set.Icc (-Real.pi / 2) (0) := by
          have h₇₆ : α + β - 2 * Real.pi > -Real.pi / 2 := by
            nlinarith [Real.pi_pos, h₇₁, h₇₂]
          have h₇₇ : α + β - 2 * Real.pi < (0: ℝ) := by
            nlinarith [Real.pi_pos, h₇₁, h₇₂]
          constructor <;> linarith
        have h₇₈ : Real.cos (α + β) = Real.cos (α + β - 2 * Real.pi) := by
          have h : Real.cos (α + β) = Real.cos (α + β - 2 * Real.pi) := by
            have h1 : α + β - 2 * Real.pi = (α + β) - 2 * Real.pi := by ring
            rw [h1]
            rw [Real.cos_sub_two_pi]
          assumption
        have h₇₉ : Real.cos (α + β - 2 * Real.pi) > 0 := by
          have h₇₇₀ : -Real.pi / 2 < α + β - 2 * Real.pi := by
            have h₇₇₁ : α + β - 2 * Real.pi > -Real.pi / 2 := by
              nlinarith [Real.pi_pos, h₇₁, h₇₂]
            linarith
          have h₆₇₇₁ : α + β - 2 * Real.pi < (0 : ℝ) := by
            nlinarith [Real.pi_pos, h₇₁, h₇₂]
          have h₇₇₃ : α + β - 2 * Real.pi < Real.pi / 2 := by
            nlinarith [Real.pi_pos, h₇₁, h₇₂]
          have h₇₇₄ : Real.cos (α + β - 2 * Real.pi) > 0 := by
            apply Real.cos_pos_of_mem_Ioo
            constructor
            · -- Show -π/2 < α+β-2π
              linarith
            · -- Show α+β-2π < π/2
              linarith
          linarith
        have h₇₇₀ : Real.cos (α + β) > 0 := by
          linarith
        linarith
      linarith
    have h₄₀ : Real.cos (α + β) = 4 / 5 := by
      nlinarith [Real.sqrt_nonneg (Real.cos (α + β) ^ 2), h₇, h₈, Real.sq_sqrt (show (0 : ℝ) ≤ (4 / 5 : ℝ) by norm_num)]
    exact_mod_cast h₄₀

  have h₇ : Real.cos (β - Real.pi / 4) = -5 / 13 := by
    have h₈ : Real.cos (β - Real.pi / 4) ^ 2 + Real.sin (β - Real.pi / 4) ^ 2 = 1 := Real.cos_sq_add_sin_sq (β - Real.pi / 4)
    rw [h₄] at h₈
    have h₉ : Real.cos (β - Real.pi / 4) < 0 := by
      have h₁₀ : β - Real.pi / 4 > Real.pi / 2 := by
        nlinarith [Real.pi_pos, h₂₁, h₂₂]
      have h₁₁ : β - Real.pi / 4 < 3 * Real.pi / 4 := by
        nlinarith [Real.pi_pos, h₂₁, h₂₂]
      have h₁₂ : Real.cos (β - Real.pi / 4) < 0 := by
        apply Real.cos_neg_of_pi_div_two_lt_of_lt
        all_goals linarith [Real.pi_pos]
      linarith
    have h₇ : Real.cos (β - Real.pi / 4) = -5 / 13 := by
      nlinarith [Real.sqrt_nonneg (Real.cos (β - Real.pi / 4) ^ 2), h₈, h₉]
    exact_mod_cast h₇

  have h₆ : Real.cos (α + Real.pi / 4) = Real.cos (α + β) * Real.cos (β - Real.pi / 4) + Real.sin (α + β) * Real.sin (β - Real.pi / 4) := by
    have h₇ : α + Real.pi / 4 = (α + β) - (β - Real.pi / 4) := by
      ring
    rw [h₇]
    rw [Real.cos_sub]
    all_goals ring_nf
    all_goals try simp [Real.sin_sq] <;> nlinarith
    all_goals try nlinarith [Real.sin_sq_add_cos_sq (α + β), Real.sin_sq_add_cos_sq (β - Real.pi / 4)]
    all_goals try tauto

  rw [h₆, h₅, h₇, h₃, h₄]
  all_goals norm_num
  all_goals nlinarith
  <;> linarith