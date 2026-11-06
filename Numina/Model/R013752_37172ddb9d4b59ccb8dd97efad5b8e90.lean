import Mathlib

open Real Set
open scoped Real

theorem algebra_326471 (θ : ℝ) (hθ : θ ∈ Ioo 0 (π / 2)) :
    IsLeast {x | ∃ θ : ℝ, θ ∈ Ioo 0 (π / 2) ∧ x = sin θ ^ 2 / cos θ + cos θ ^ 2 / sin θ} (sqrt 2) ∧
    ∀ x, ∃ θ : ℝ, θ ∈ Ioo 0 (π / 2) ∧ x = sin θ ^ 2 / cos θ + cos θ ^ 2 / sin θ → x ≥ sqrt 2 := by
  constructor
  · -- Show that √2 is the least in the range
    constructor
    · -- Show that √2 is attained
      use Real.pi / 4
      constructor
      · -- Show that pi/4 is in (0, pi/2)
        exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      · -- Calculate f(pi/4) and show it equals sqrt 2
        have h1 : sin (Real.pi / 4) = sqrt 2 / 2 := by
          rw [sin_pi_div_four]
        have h2 : cos (Real.pi / 4) = sqrt 2 / 2 := by
          rw [cos_pi_div_four]
        rw [h1, h2]
        field_simp
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ))) (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)))]
    · -- Show that ∀ x ∈ range, x ≥ sqrt 2
      intro x hx
      rcases hx with ⟨θ, hθ, heq⟩
      rcases hθ with ⟨h11, h12⟩
      rw [heq]
      have h21 : 0 < sin θ := by
        apply sin_pos_of_pos_of_lt_pi
        linarith [Real.pi_pos, h11, h12]
        linarith [Real.pi_pos, h11, h12]
      have h22 : 0 < cos θ := by
        have h2 : θ < Real.pi / 2 := h12
        have h3 : cos θ > 0 := by
          apply cos_pos_of_mem_Ioo
          constructor <;> linarith [Real.pi_pos, h2]
        exact h3
      have h4 : sin θ ^ 2 / cos θ + cos θ ^ 2 / sin θ >= Real.sqrt 2 := by
        have h5 : sin θ ^ 2 / cos θ + cos θ ^ 2 / sin θ = (sin θ ^ 3 + cos θ ^ 3) / (sin θ * cos θ) := by
          field_simp [show cos θ ≠ 0 by linarith, show sin θ ≠ 0 by linarith]
          <;> ring
        rw [h5]
        have h1sin : 0 < sin θ * cos θ := mul_pos h21 h22
        have h33 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
          linarith [Real.sin_sq_add_cos_sq θ]
        have h51 : (sin θ ^ 3 + cos θ ^ 3) / (sin θ * cos θ) >= Real.sqrt 2 := by
          have h52 : (sin θ ^ 3 + cos θ ^ 3) >= Real.sqrt 2 * (sin θ * cos θ) := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2, sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ + cos θ - Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), mul_pos h21 h22, sq_nonneg (sin θ ^ 2 - cos θ ^ 2), sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ + cos θ), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (sin θ ^ 2 + cos θ ^ 2 - 1)]
          have h53 : (sin θ ^ 3 + cos θ ^ 3) / (sin θ * cos θ) >= Real.sqrt 2 := by
            apply (le_div_iff₀ h1sin).mpr
            nlinarith
          linarith
        linarith
      linarith
  · -- Show theorem's second part as vacuous
    intro x
    use Real.pi / 4
    intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨h11, h12⟩
    have h1 : sin (Real.pi / 4) = sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h2' : cos (Real.pi / 4) = sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    rw [h1, h2'] at h2
    field_simp at h2
    <;> nlinarith [Real.sqrt_nonneg 2, mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ))) (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ))), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ))]