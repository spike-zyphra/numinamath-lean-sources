import Mathlib

open Real

theorem algebra_21880 (perimeter : ℝ) (hp : 0 < perimeter) (f r : ℝ → ℝ)
    (hr : ∀ θ, θ ∈ Set.Ioo 0 π → 2 * r θ + θ * r θ = perimeter)
    (hf : ∀ θ, θ ∈ Set.Ioo 0 π → f θ = (r θ) ^ 2 * θ / 2) :
    IsMaxOn f (Set.Ioo 0 π) 2 := by
  unfold IsMaxOn
  intro θ hθ
  have hθ1 : 0 < θ := hθ.1
  have hθ2 : θ < Real.pi := hθ.2
  have h1 : r θ = perimeter / (2 + θ) := by
    have h_eq : 2 * r θ + θ * r θ = perimeter := by 
      apply hr θ 
      exact ⟨by linarith, by linarith [Real.pi_gt_three]⟩
    have h2 : r θ * (2 + θ) = perimeter := by 
      nlinarith 
    have h3 : r θ = perimeter / (2 + θ) := by 
      have hθ : θ > 0 := hθ1 
      have hθ3 : θ < Real.pi := hθ2 
      field_simp [(show (2 + θ) ≠ 0 by linarith)] at * 
      all_goals nlinarith 
    exact h3
  have h2 : f θ = (perimeter / (2 + θ)) ^ 2 * θ / 2 := by 
    rw [hf θ ⟨by linarith, by linarith [Real.pi_gt_three]⟩]
    rw [h1]
  have h3 : f 2 = (perimeter / 4) ^ 2 * 2 / 2 := by
    have h2_in : (2 : ℝ) ∈ Set.Ioo (0 : ℝ) Real.pi := by
      constructor
      · norm_num 
      · linarith [Real.pi_gt_three]
    rw [hf 2 h2_in]
    have h_r2 : r 2 = perimeter / 4 := by 
      have h2_1 : 2 * r 2 + 2 * r 2 = perimeter := by 
        apply hr 2 
        exact ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
      field_simp [(show (2 + 2 : ℝ) ≠ 0 by norm_num)] at h2_1 ⊢
      linarith 
    rw [h_r2]
  have h4 : f θ ≤ f 2 := by
    rw [h2, h3]
    have h0 : 0 < 2 + θ := by nlinarith
    have h1 : 0 < 2 + θ := by linarith
    have hp2 : 0 < perimeter := hp
    have hr1 : θ ^ 2 - 4 * θ + 4 ≥ 0 := by
      nlinarith [sq_nonneg (θ - 2)]
    have h7 : (perimeter / (2 + θ)) ^ 2 * θ / 2 ≤ (perimeter / 4) ^ 2 * 2 / 2 := by
      have h9 : 0 < perimeter := hp
      have h4 : 0 < (2 + θ) ^ 2 := by positivity
      have h2 : 0 < 16 := by norm_num
      have h11 : θ ^ 2 - 4 * θ + 4 ≥ 0 := by
        nlinarith [sq_nonneg (θ - 2)]
      have h10 : (perimeter / (2 + θ)) ^ 2 * θ / 2 - ((perimeter / 4) ^ 2 * 2 / 2) ≤ 0 := by
        have h11 : (perimeter / (2 + θ)) ^ 2 * θ / 2 - ((perimeter / 4) ^ 2 * 2 / 2) =
            (perimeter ^ 2 * θ - perimeter ^ 2 / 16 * 2 * (2 + θ)  ^ 2) / (2 * (2 + θ) ^ 2) := by
          field_simp
          ring
        rw [h11]
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Show that the numerator is less than or equal to 0
          nlinarith [sq_nonneg (perimeter ^ 2), sq_nonneg (θ - 2), sq_pos_of_pos hp]
        · -- Show that the denominator is non-negative
          positivity
      linarith
    linarith
  exact h4