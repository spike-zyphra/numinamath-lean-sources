import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_196715 (φ : ℝ) (hφ : 0 < φ ∧ φ < π/4) :
    ∑' n : ℕ, (-tan φ)^n = sqrt 2 * cos φ / (2 * sin (π/4 + φ)) := by
  rcases hφ with ⟨h1, h2⟩
  have h3 : cos φ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h4 : sin φ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have htan : |tan φ| < 1 := by
    have htan1 : tan φ = sin φ / cos φ := by
      rw [tan_eq_sin_div_cos]
    have htan2 : tan φ > 0 := by
      rw [tan_eq_sin_div_cos]
      apply div_pos
      linarith [h4]
      linarith [h3]
    have htan3 : tan φ < 1 := by
      have htan4 : tan (π / 4) = 1 := by
        rw [tan_pi_div_four]
      have htan5 : tan φ < tan (π / 4) := by
        apply Real.tan_lt_tan_of_lt_of_lt_pi_div_two
        all_goals
          nlinarith [h1, h2, Real.pi_pos]
      have htan6 : tan (π / 4) = 1 := by
        rw [tan_pi_div_four]
      linarith [htan5, htan6]
    have htan7 : |tan φ| = tan φ := by
      rw [abs_of_pos htan2]
    rw [htan7]
    linarith [htan3]
  have h5 : ∑' n : ℕ, (-tan φ)^n = 1 / (1 + tan φ) := by
    have h6 : |(-tan φ : ℝ)| < (1 : ℝ) := by
      have h8 : |(-tan φ : ℝ)| = |tan φ| := by
        rw [show (-tan φ : ℝ) = - (tan φ : ℝ) by ring]
        rw [abs_neg]
      rw [h8]
      linarith [htan]
    rw [tsum_geometric_of_norm_lt_one h6]
    field_simp
  have h7 : sin (π / 4 + φ) = sin (π / 4) * cos φ + cos (π / 4) * sin φ := by
    rw [sin_add]
  have h8 : sin (π / 4) = Real.sqrt 2 / 2 := by
    rw [sin_pi_div_four]
  have h9 : cos (π / 4) = Real.sqrt 2 / 2 := by
    rw [cos_pi_div_four]
  have h10 : sin (π / 4 + φ) = Real.sqrt 2 / 2 * (cos φ + sin φ) := by
    rw [h7, h8, h9]
    all_goals
      ring_nf 
  -- Show that the right-hand side is equal to cos φ / (cos φ + sin φ)
  have h11 : sqrt 2 * cos φ / (2 * sin (π / 4 + φ)) = cos φ / (cos φ + sin φ) := by
    rw [h10]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num), Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  rw [h5]
  rw [h11]
  have htan2 : 1 + tan φ = (cos φ + sin φ) / cos φ := by
    have htan3 : tan φ = sin φ / cos φ := by
      rw [tan_eq_sin_div_cos]
    rw [htan3]
    field_simp
  field_simp [htan2, h3]
  <;> nlinarith