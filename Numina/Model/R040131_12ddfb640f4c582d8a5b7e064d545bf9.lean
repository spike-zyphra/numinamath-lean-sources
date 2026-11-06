import Mathlib

open Real Set
open scoped Real

theorem algebra_158124 (θ : ℝ) (hθ : θ ∈ Ioo 0 (π/2)) :
    (1/sin θ - 1) * (1/cos θ - 1) ≤ 3 - 2*sqrt 2 := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : sin θ > 0 := by 
    apply sin_pos_of_mem_Ioo
    constructor
    · linarith [h1, Real.pi_pos]
    · nlinarith [h2, Real.pi_pos]

  have h4 : cos θ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h1, Real.pi_pos]
    · nlinarith [h2, Real.pi_pos]

  have h5 : (1/sin θ - 1) * (1/cos θ - 1) = 
      (1 - sin θ - cos θ + sin θ * cos θ) / (sin θ * cos θ) := by
    field_simp
    <;> ring
  have h6 : sin θ * cos θ > 0 := mul_pos h3 h4

  have h7 : (1/sin θ - 1) * (1/cos θ - 1) ≤ 3 - 2*sqrt 2 := by
    rw [h5]
    have h10 : sin θ * cos θ > 0 := h6
    apply (div_le_iff₀ h10).mpr
    nlinarith [sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ + cos θ - 1), 
      sq_nonneg (sin θ + cos θ - sqrt 2), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), 
      sq_nonneg (sin θ^2 + cos θ^2 - 1), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      sq_nonneg (sqrt 2 ^ 2 - 2), Real.sqrt_nonneg (2 : ℝ), 
      Real.sin_sq_add_cos_sq θ, h3, h4
    ]
  linarith