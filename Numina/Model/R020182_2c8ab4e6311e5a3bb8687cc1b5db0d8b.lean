import Mathlib

open Real Set
open scoped Real

theorem algebra_230007 (α β : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : cos (α + β) = -4 / 5) (x y : ℝ) (hx : x = sin β) (hy : y = cos α) :
    y = -4 / 5 * sqrt (1 - x ^ 2) + 3 / 5 * x ∧ 4 / 5 < x ∧ x < 1 := by
  rcases h₀ with ⟨h₀₀, h₀₁⟩
  rcases h₁ with ⟨h₁₀, h₁₁⟩
  have h3 : sin (α + β) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos, h₀₀, h₀₁, h₁₀, h₁₁]
    linarith [Real.pi_pos, h₀₀, h₀₁, h₁₀, h₁₁]
  have h4 : sin (α + β) = 3 / 5 := by
    have h4 : sin (α + β) ^ 2 + cos (α + β) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (α + β)
    rw [h₂] at h4
    have h4 : sin (α + β) ^ 2 = 1 - ( -4 / 5) ^ 2 := by linarith
    have h4 : sin (α + β) ^ 2 = 9 / 25 := by
      nlinarith
    nlinarith
  have h5 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos, h₀₀, h₀₁, h₁₀, h₁₁]
    linarith [Real.pi_pos, h₀₀, h₀₁, h₁₀, h₁₁]
  have h6 : cos β > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos, h₁₀, h₁₁]
    linarith [Real.pi_pos, h₁₀, h₁₁]
  have hx1 : x > 0 := by
    have h7 : sin β = x := by linarith [hx]
    have h8 : sin β > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos, h₀₀, h₀₁, h₁₀, h₁₁]
      linarith [Real.pi_pos, h₀₀, h₀₁, h₁₀, h₁₁]
    nlinarith
  have hy1 : y > 0 := by
    have h7 : cos α = y := by linarith [hy]
    have h8 : cos α > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith [Real.pi_pos, h₀₀, h₀₁, h₁₀, h₁₁]
      linarith [Real.pi_pos, h₀₀, h₀₁, h₁₀, h₁₁]
    nlinarith
  have h7 : sin α = Real.sqrt (1 - y ^ 2) := by
    have h8 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact sin_sq_add_cos_sq α
    have h9 : cos α = y := by linarith [hy]
    have h9 : sin α ^ 2 = 1 - y ^ 2 := by
      rw [h9] at h8
      linarith
    have h10 : sin α > 0 := h5
    have h11 : sin α = Real.sqrt (1 - y ^ 2) := by
      have h11 : sin α > 0 := h5
      have h13 : 1 - y ^ 2 ≥ 0 := by
        nlinarith [sq_pos_of_pos h11, h8]
      have h11 : sin α = Real.sqrt (1 - y ^ 2) := by
        have h13 : sin α ^ 2 = 1 - y ^ 2 := h9
        have h14 : sin α ≥ 0 := by linarith
        rw [←h13]
        field_simp [Real.sqrt_sq_eq_abs, abs_of_pos h11]
      linarith
    linarith
  have h8 : cos β = Real.sqrt (1 - x ^ 2) := by
    have h9 : sin β ^ 2 + cos β ^ 2 = 1 := by
      exact sin_sq_add_cos_sq β
    have h9 : sin β = x := by linarith [hx]
    have h9 : cos β ^ 2 = 1 - x ^ 2 := by
      rw [h9] at h9
      nlinarith
    have h10 : cos β > 0 := h6
    have h11 : cos β = Real.sqrt (1 - x ^ 2) := by
      have h11 : cos β > 0 := h6
      have h13 : 1 - x ^ 2 ≥ 0 := by
        nlinarith [sq_pos_of_pos h11, h9]
      have h11 : cos β = Real.sqrt (1 - x ^ 2) := by
        have h13 : cos β ^ 2 = 1 - x ^ 2 := h9
        have h14 : cos β ≥ 0 := by linarith
        rw [←h13]
        field_simp [Real.sqrt_sq_eq_abs, abs_of_pos h11]
      linarith
    linarith
  have eq1 : cos α * cos β - sin α * sin β = -4 / 5 := by
    have h9 : cos (α + β) = cos α * cos β - sin α * sin β := by
      rw [cos_add]
    linarith [h₂, h9]
  have eq2 : sin α * cos β + cos α * sin β = 3 / 5 := by
    have h9 : sin (α + β) = sin α * cos β + cos α * sin β := by
      rw [sin_add]
    linarith [h4, h9]
  rw [show cos α = y by linarith [hy]] at eq1 eq2
  rw [show sin β = x by linarith [hx]] at eq1 eq2
  rw [h7] at eq1 eq2
  rw [h8] at eq1 eq2
  have h9 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [show x < 1 by nlinarith [sin_sq_add_cos_sq β, Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith) (show β < Real.pi by linarith), show cos β > 0 by linarith]]
  have h10 : Real.sqrt (1 - y ^ 2) ^ 2 = 1 - y ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [show y < 1 by nlinarith [cos_sq_add_sin_sq α, Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith) (show α < Real.pi by linarith), show sin α > 0 by linarith]]
  constructor
  · -- Show the functional relationship between y and x
    nlinarith [Real.sqrt_nonneg (1 - x ^ 2), Real.sqrt_nonneg (1 - y ^ 2), 
      h9, h10
    ]
  · -- Show the bounds for x
    constructor
    · -- Show the lower bound
      nlinarith [Real.sqrt_nonneg (1 - x ^ 2), Real.sqrt_nonneg (1 - y ^ 2), 
        h9, h10
      ]
    · -- Show the upper bound
      nlinarith [Real.sqrt_nonneg (1 - x ^ 2), Real.sqrt_nonneg (1 - y ^ 2), 
        h9, h10
      ]