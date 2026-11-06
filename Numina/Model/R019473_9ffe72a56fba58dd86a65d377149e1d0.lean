import Mathlib

open Real

theorem algebra_191798 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) (f : ℝ → ℝ)
    (hf : f = fun x => logb a x) (x₁ x₂ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    (a > 1 → (1 / 2) * (f x₁ + f x₂) ≤ f ((x₁ + x₂) / 2)) ∧
    (0 < a ∧ a < 1 → (1 / 2) * (f x₁ + f x₂) ≥ f ((x₁ + x₂) / 2)) := by
  constructor
  · -- First case: a > 1, need to show that $(1/2) * (f(x₁) + f(x₂)) ≤ f((x₁ + x₂)/2)$
    intro ha2
    have h1 : f x₁ = logb a x₁ := by
      rw [hf]
    have h2 : f x₂ = logb a x₂ := by
      rw [hf]
    have h3 : f ((x₁ + x₂) / 2) = logb a ((x₁ + x₂) / 2) := by
      rw [hf]
    rw [h1, h2, h3]
    have h4 : logb a x₁ + logb a x₂ = logb a (x₁ * x₂) := by
      rw [← logb_mul (by positivity) (by positivity)]
    have h5 : (1 / 2 : ℝ) * (logb a x₁ + logb a x₂) = logb a ((x₁ * x₂) ^ (1 / 2 : ℝ)) := by
      rw [h4]
      rw [← logb_rpow_eq_mul_logb_of_pos]
      ring_nf
      all_goals try positivity
    rw [h5] at *
    have h6 : logb a ((x₁ * x₂) ^ (1 / 2 : ℝ)) ≤ logb a ((x₁ + x₂) / 2) := by
      have h10 : (x₁ * x₂) ^ (1 / 2 : ℝ) = Real.sqrt (x₁ * x₂) := by
        rw [Real.sqrt_eq_rpow]
      rw [h10]
      have h11 : Real.sqrt (x₁ * x₂) ≤ (x₁ + x₂) / 2 := by
        have h12 : (Real.sqrt (x₁ * x₂)) ^ 2 ≤ ((x₁ + x₂) / 2) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x₁ * x₂), Real.sq_sqrt (show (0 : ℝ) ≤ x₁ * x₂ by positivity), sq_nonneg (x₁ - x₂)]
        have h13 : Real.sqrt (x₁ * x₂) ≥ 0 := by positivity
        have h14 : (x₁ + x₂) / 2 ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (x₁ * x₂), sq_nonneg (Real.sqrt (x₁ * x₂) - (x₁ + x₂) / 2)]
      have h100 : Real.sqrt (x₁ * x₂) > 0 := by positivity
      have h110 : (x₁ + x₂) / 2 > 0 := by positivity
      have h120 : logb a (Real.sqrt (x₁ * x₂)) ≤ logb a ((x₁ + x₂) / 2) := by
        apply Real.logb_le_logb_of_le
        all_goals try linarith
        all_goals try nlinarith
      linarith
    linarith [h6, show 0 < a by linarith, show a > 1 by linarith]
    all_goals try linarith
    all_goals try nlinarith
  · -- Second case
    rintro ⟨ha0, ha1⟩
    have h1 : f x₁ = logb a x₁ := by
      rw [hf]
    have h2 : f x₂ = logb a x₂ := by
      rw [hf]
    have h3 : f ((x₁ + x₂) / 2) = logb a ((x₁ + x₂) / 2) := by
      rw [hf]
    rw [h1, h2, h3]
    have h4 : logb a x₁ + logb a x₂ = logb a (x₁ * x₂) := by
      rw [← logb_mul (by positivity) (by positivity)]
    have h5 : (1 / 2 : ℝ) * (logb a x₁ + logb a x₂) = logb a ((x₁ * x₂) ^ (1 / 2 : ℝ)) := by
      rw [h4]
      rw [← logb_rpow_eq_mul_logb_of_pos]
      ring_nf
      all_goals try positivity
    rw [h5] at *
    have h6 : logb a ((x₁ * x₂) ^ (1 / 2 : ℝ)) ≥ logb a ((x₁ + x₂) / 2) := by
      have h10 : (x₁ * x₂) ^ (1 / 2 : ℝ) = Real.sqrt (x₁ * x₂) := by
        rw [Real.sqrt_eq_rpow]
      rw [h10]
      have h11 : Real.sqrt (x₁ * x₂) ≤ (x₁ + x₂) / 2 := by
        have h12 : (Real.sqrt (x₁ * x₂)) ^ 2 ≤ ((x₁ + x₂) / 2) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x₁ * x₂), Real.sq_sqrt (show (0 : ℝ) ≤ x₁ * x₂ by positivity), sq_nonneg (x₁ - x₂)]
        have h13 : Real.sqrt (x₁ * x₂) ≥ 0 := by positivity
        have h14 : (x₁ + x₂) / 2 ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (x₁ * x₂), sq_nonneg (Real.sqrt (x₁ * x₂) - (x₁ + x₂) / 2)]
      have h100 : Real.sqrt (x₁ * x₂) > 0 := by positivity
      have h110 : (x₁ + x₂) / 2 > 0 := by positivity
      have h120 : logb a (Real.sqrt (x₁ * x₂)) ≥ logb a ((x₁ + x₂) / 2) := by
        have h140 : logb a (Real.sqrt (x₁ * x₂)) ≥ logb a ((x₁ + x₂) / 2) := by
          have h153 : logb a (Real.sqrt (x₁ * x₂)) = (log (Real.sqrt (x₁ * x₂))) / (log a) := by field_simp [logb]
          have h154 : logb a ((x₁ + x₂) / 2) = (log ((x₁ + x₂) / 2)) / (log a) := by field_simp [logb]
          rw [h153, h154]
          have h256 : log a < 0 := by
            have : log a < log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals nlinarith
            have h366 : log (1 : ℝ) = 0 := Real.log_one
            linarith
          have h377 : log (Real.sqrt (x₁ * x₂)) ≤ log ((x₁ + x₂) / 2) := by
            apply Real.log_le_log
            all_goals try positivity
            all_goals try nlinarith
          have h388 : (log (Real.sqrt (x₁ * x₂))) / (log a) ≥ (log ((x₁ + x₂) / 2)) / (log a) := by
            apply (div_le_div_right_of_neg h256).mpr
            all_goals try nlinarith
          linarith
        linarith
      linarith
    linarith [h6, show 0 < a by linarith, show a < 1 by linarith]
    all_goals try linarith
    all_goals try nlinarith