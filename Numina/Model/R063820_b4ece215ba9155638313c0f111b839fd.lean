import Mathlib

theorem other_275221 {p : ℝ} (hp : p ∈ Set.Icc 0 1) (h : 60 / (0.8 * (1 - p)) = 20 / (0.15 * p)) :
    p = 0.64 := by
  have h1 : 0 ≤ p ∧ p ≤ 1 := by 
    exact hp
  have hp1 : 0 < p := by
    by_contra h2
    push_neg at h2
    have h3 : 0.15 * p ≤ (0 : ℝ) := by
      nlinarith
    have h4 : 0.8 * (1 - p) > 0 := by
      have hp1 : 1 - p > 0 := by nlinarith [h1.left, h2]
      positivity
    have h5 : 20 / (0.15 * p) ≤ (0 : ℝ) := by
      apply div_nonpos_of_nonneg_of_nonpos
      · norm_num
      · linarith
    have h6 : 60 / (0.8 * (1 - p)) > (0 : ℝ) := by 
      positivity
    linarith [h, h6, h5]
  have hp2 : p < 1 := by
    by_contra h3
    push_neg at h3
    have h3' : (1 - p) ≤ (0 : ℝ) := by nlinarith
    have h5 : 0.15 * p > 0 := by
      nlinarith
    have h4 : 60 / (0.8 * (1 - p)) ≤ (0 : ℝ) := by 
      apply div_nonpos_of_nonneg_of_nonpos
      · norm_num
      · nlinarith
    have h6 : 20 / (0.15 * p) > (0 : ℝ) := by 
      positivity
    linarith [h, h4, h6]
  have eq1 : 60 / (0.8 * (1 - p)) = 20 / (0.15 * p) := h
  have eq2 : 60 * (0.15 * p) = 20 * (0.8 * (1 - p)) := by
    field_simp [(show 0.8 * (1 - p) ≠ 0 by
      by_contra h2
      have h2' : (0.8 * (1 - p) ) = 0 := by
        linarith [h2]
      have hp_eq : 1 - p = 0 := by
        ring_nf at h2'
        <;> nlinarith
      have hp_eq_p : p = 1 := by
        nlinarith
      linarith [hp_eq_p, hp2]
    ), (show 0.15 * p ≠ 0 by
      by_contra h2
      have h2' : (0.15 * p) = 0 := by
        linarith [h2]
      have hp_eq : p = 0 := by
        nlinarith
      linarith [hp_eq, hp1]
    )] at eq1 ⊢
    nlinarith
  ring_nf at eq2 ⊢
  nlinarith [h1.1, h1.2]