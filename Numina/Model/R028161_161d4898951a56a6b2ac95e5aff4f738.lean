import Mathlib

open Real Set
open scoped Real

theorem algebra_12330 {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) (h : 1/sin θ + 1/cos θ = 35/12) :
    tan θ = 4/3 ∨ tan θ = 3/4 := by
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
  have h5 : sin θ ≠ 0 := by linarith [h3]
  have h6 : cos θ ≠ 0 := by linarith [h4]
  have eq1 : cos θ + sin θ = (35 / 12) * (sin θ * cos θ) := by
    field_simp [h5, h6] at h ⊢
    nlinarith
  have h9 : ( (35 / 12) * (sin θ * cos θ) )^2 = 1 + 2 * (sin θ * cos θ) := by
    nlinarith [sq_nonneg (sin θ - cos θ), Real.sin_sq_add_cos_sq θ, eq1]
  have h12 : (sin θ * cos θ) > 0 := by
    nlinarith [h3, h4]
  have h13 : (sin θ * cos θ) = 12 / 25 := by
    nlinarith [sq_nonneg (sin θ - cos θ), h12, eq1, Real.sin_sq_add_cos_sq θ, h9]
  have h14 : (cos θ + sin θ) = 7 / 5 := by
    nlinarith [h13, Real.sin_sq_add_cos_sq θ, eq1]
  have h15 : (sin θ - 4 / 5) * (sin θ - 3 / 5) = 0 := by
    nlinarith [sq_nonneg (sin θ - cos θ), Real.sin_sq_add_cos_sq θ, h14, h13]
  cases' (mul_eq_zero.mp h15) with h16 h17
  · -- Case $\sin \theta = \frac{4}{5}$
    have h18 : sin θ = 4 / 5 := by linarith
    have h19 : cos θ = 3 / 5 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, h18, h14]
    have htan : tan θ = 4 / 3 := by
      rw [tan_eq_sin_div_cos]
      rw [h18, h19]
      norm_num
    left
    exact htan
  · -- Case $\sin \theta = \frac{3}{5}$
    have h20 : sin θ = 3 / 5 := by linarith
    have h21 : cos θ = 4 / 5 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, h20, h14]
    have htan : tan θ = 3 / 4 := by
      rw [tan_eq_sin_div_cos]
      rw [h20, h21]
      norm_num
    right
    exact htan