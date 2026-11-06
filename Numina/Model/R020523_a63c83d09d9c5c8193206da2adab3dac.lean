import Mathlib

open Real Set
open scoped Real

theorem algebra_13002 {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) (h : 3 * (sin θ)^2 + 5 * sin θ * cos θ - 4 * (cos θ)^2 = 2) :
    θ = π / 4 := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : sin θ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h4 : cos θ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h_eq : sin θ = cos θ := by
    have eq1 : 3 * (sin θ) ^ 2 + 5 * sin θ * cos θ - 4 * (cos θ) ^ 2 = 2 := by linarith
    have eq2 : (sin θ) ^ 2 + (cos θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ + cos θ), 
          mul_pos h3 h4, sq_pos_of_pos h3, sq_pos_of_pos h4
        ]
  have eq5 : θ = π / 4 := by
    have eq6 : sin θ = cos θ := h_eq
    have h3 : sin θ > 0 := h3
    have h4 : cos θ > 0 := h4
    have eq8 : sin θ = Real.sqrt 2 / 2 := by
      have h_eq4 : sin θ ^ 2 = 1 / 2 := by
        nlinarith [Real.sin_sq_add_cos_sq θ, eq6, sq_pos_of_pos h3, sq_pos_of_pos h4]
      have h3' : sin θ > 0 := by linarith [h3]
      have h4' : sin θ = Real.sqrt (1 / 2) := by
        rw [← h_eq4]
        field_simp
        <;> nlinarith
      have h5' : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h5', h4']
    have eq11 : θ = π / 4 := by
      have eq11 : sin θ = Real.sqrt 2 / 2 := eq8
      have eq12 : θ > 0 := by linarith [h1]
      have eq13 : θ < π / 2 := by linarith [h2]
      have eq14 : θ = π / 4 := by
        have eq15 : sin θ = Real.sqrt 2 / 2 := eq11
        have h14 : θ = π / 4 := by
          have h56 : θ > 0 := by nlinarith
          have h57 : θ < Real.pi / 2 := by nlinarith
          have eq16 : θ = Real.arcsin (Real.sqrt 2 / 2) := by
            rw [← eq15]
            apply Eq.symm
            apply Real.arcsin_sin
            all_goals
              nlinarith [Real.pi_pos]
          have eq17 : Real.arcsin (Real.sqrt 2 / 2) = π / 4 := by
            have h62 : sin (π / 4) = Real.sqrt 2 / 2 := by
              rw [sin_pi_div_four]
            have h63 : arcsin (sin (π / 4)) = π / 4 := by
              apply arcsin_sin
              all_goals linarith [Real.pi_pos]
            have h64 : arcsin (Real.sqrt 2 / 2) = π / 4 := by
              rw [show Real.sqrt 2 / 2 = sin (π / 4) by linarith [h62]] 
              all_goals linarith [h63]
            linarith [h64]
          rw [eq17] at eq16
          linarith
        assumption
      assumption
    assumption
  exact eq5