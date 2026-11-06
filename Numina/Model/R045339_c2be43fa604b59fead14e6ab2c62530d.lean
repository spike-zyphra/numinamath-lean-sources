import Mathlib

open Real Set
open scoped Real

theorem algebra_9003 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin x + cos x)
(θ : ℝ) (fmin: ∀x:ℝ, f x ≥ f θ) (hθ' : deriv f θ = 0) : cos (θ + π / 4) = sqrt 10 / 10 := by
  have h1 : f = λ x => 2 * sin x + cos x := by exact_mod_cast hf
  have h2 : deriv f θ = 2 * cos θ - sin θ := by
    rw [h1]
    simp [deriv_add, deriv_mul, deriv_id'', mul_comm]
    all_goals ring
  rw [h2] at hθ'
  have h3 : sin θ = 2 * cos θ := by linarith
  have h4 : sin θ ^ 2 + cos θ ^ 2 = 1 := by exact Real.sin_sq_add_cos_sq θ
  rw [h3] at h4
  have h5 : cos θ ^ 2 = 1 / 5 := by
    nlinarith
  have h6 : cos θ ≤ 0 := by
    have h7 : f (θ + π / 2) ≥ f θ := by
      apply fmin
    have h8 : f (θ + π / 2) = 2 * sin (θ + π / 2) + cos (θ + π / 2) := by 
      rw [h1]
    have h9 : f θ = 2 * sin θ + cos θ := by 
      rw [h1]
    rw [h8, h9] at h7
    have h10 : sin (θ + π / 2) = cos θ := by 
      rw [sin_add_pi_div_two]
    have h11 : cos (θ + π / 2) = - sin θ := by 
      rw [cos_add_pi_div_two]
    rw [h10, h11] at h7
    nlinarith [h3]
  have h7 : cos θ = - Real.sqrt 5 / 5 := by
    have h8 : cos θ ^ 2 = 1 / 5 := h5
    have h9 : cos θ ≤ 0 := h6
    have h10 : cos θ = - Real.sqrt 5 / 5 := by
      have h13 : cos θ ^ 2 = (1 / 5 : ℝ) := h8
      have h14 : cos θ ≤ 0 := h9
      have h15 : cos θ = - Real.sqrt 5 / 5 := by
        have h16 : Real.sqrt 5 ^ 2 = 5 := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        nlinarith [Real.sqrt_nonneg 5, sq_nonneg (cos θ + Real.sqrt 5 / 5), sq_nonneg (cos θ - Real.sqrt 5 / 5), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      linarith
    linarith
  have h9 : cos (θ + π / 4) = cos θ * cos (π / 4) - sin θ * sin (π / 4) := by 
    rw [cos_add]
  rw [h9]
  have h10 : cos (π / 4) = Real.sqrt 2 / 2 := by 
    rw [cos_pi_div_four]
  have h11 : sin (π / 4) = Real.sqrt 2 / 2 := by 
    rw [sin_pi_div_four]
  rw [h10, h11, h3, h7]
  have h15 : Real.sqrt 10 = Real.sqrt 2 * Real.sqrt 5 := by
    have h16 : Real.sqrt 10 = Real.sqrt (2 * 5) := by norm_num
    rw [h16]
    rw [Real.sqrt_mul (by norm_num)]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0), Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (10 : ℝ) ≥ 0)]