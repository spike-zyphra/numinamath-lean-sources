import Mathlib

theorem algebra_301967 (a : ℤ) (x₁ x₂ : ℝ)
    (h₁ : x₁^2 + (2 * a - 1) * x₁ + a^2 = 0) (h₂ : x₂^2 + (2 * a - 1) * x₂ + a^2 = 0)
    (h₃ : x₁ ≠ x₂) :
    |Real.sqrt x₁ - Real.sqrt x₂| = 1 := by
  have h6 : x₁^2 + (2 * a - 1) * x₁ + a^2 - (x₂^2 + (2 * a - 1) * x₂ + a^2) = 0 := by linarith
  have h7 : (x₁ - x₂) * (x₁ + x₂ + (2 * a - 1)) = 0 := by 
    ring_nf at h6 ⊢
    nlinarith
  have h8 : x₁ + x₂ + (2 * a - 1) = 0 := by 
    apply (mul_left_inj' (show (x₁ - x₂) ≠ 0 by
      intro h'
      apply h₃
      linarith
    )).mp
    linarith [h7]
  have h9 : x₁ + x₂ = (1 - 2 * a : ℝ) := by linarith
  have h10 : x₁ * x₂ = (a : ℝ) ^2 := by 
    nlinarith [sq_pos_of_ne_zero (show (x₁ - x₂ : ℝ) ≠ 0 by 
      intro h'
      apply h₃
      linarith
    ), sq_nonneg (x₁ - x₂)]
  have h11 : a ≤ 0 := by 
    have h15 : (2 * a - 1 : ℝ) ^ 2 - 4 * (a : ℝ) ^2 ≥ 0 := by
      nlinarith [sq_pos_of_ne_zero (show (x₁ - x₂ : ℝ) ≠ 0 by
        intro h'
        apply h₃
        linarith
      ), sq_nonneg (x₁ - x₂)]
    have h16 : (a : ℝ) ≤ (1 / 4 : ℝ) := by nlinarith 
    have h17 : a ≤ 0 := by 
      by_contra h18
      push_neg at h18 
      have h19 : a ≥ 1 := by omega 
      have h20 : (a : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h19 
      nlinarith
    assumption
  have h12 : x₁ ≥ 0 := by 
    by_contra h 
    push_neg at h 
    have h13 : x₂ ≤ 0 := by 
      nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - 2 * (a : ℝ)), sq_nonneg ((a : ℝ)), h10, sq_nonneg (a : ℝ)]
    nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - 2 * (a : ℝ)), sq_nonneg ((a : ℝ)), h13, h, sq_nonneg (x₁ + x₂), sq_nonneg (a : ℝ), sq_nonneg ((a : ℝ)), h11]
  have h13 : x₂ ≥ 0 := by 
    by_contra h 
    push_neg at h 
    have h14 : x₁ ≤ 0 := by 
      nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - 2 * (a : ℝ)), sq_nonneg ((a : ℝ)), h10, sq_nonneg (a : ℝ)]
    nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - 2 * (a : ℝ)), sq_nonneg ((a : ℝ)), h14, h, sq_nonneg (x₁ + x₂), sq_nonneg (a : ℝ), sq_nonneg ((a : ℝ)), h11]
  have h14 : (Real.sqrt x₁ - Real.sqrt x₂) ^2 = 1 := by
    have h15 : Real.sqrt x₁ ^2 = x₁ := Real.sq_sqrt (show 0 ≤ x₁ by linarith)
    have h16 : Real.sqrt x₂ ^2 = x₂ := Real.sq_sqrt (show 0 ≤ x₂ by linarith)
    have h17' : Real.sqrt x₁ * Real.sqrt x₂ = - (a : ℝ) := by 
      have h18 : Real.sqrt x₁ * Real.sqrt x₂ = Real.sqrt (x₁ * x₂) := by 
        rw [← Real.sqrt_mul (by linarith)]
      have h19 : Real.sqrt (x₁ * x₂) = Real.sqrt ((a : ℝ) ^2) := by 
        rw [show x₁ * x₂ = (a : ℝ) ^2 by linarith [h10]]
      have h20 : Real.sqrt ((a : ℝ) ^2) = abs (a : ℝ) := by 
        rw [Real.sqrt_sq_eq_abs]
      have h21 : abs (a : ℝ) = - (a : ℝ) := by 
        have h21 : (a : ℝ) ≤ (0 : ℝ) := by 
          exact_mod_cast (show a ≤ (0 : ℤ) by omega)
        have h22 : abs (a : ℝ) = - (a : ℝ) := by 
          rw [abs_of_nonpos h21]
          all_goals linarith 
        linarith [h22]
      nlinarith [h18, h19, h20, h21, h12, h13]
    nlinarith [h15, h16, h17']
  have h18 : |Real.sqrt x₁ - Real.sqrt x₂| = 1 := by 
    have h15 : (Real.sqrt x₁ - Real.sqrt x₂) ^ 2 = 1 := h14
    have h16 : |Real.sqrt x₁ - Real.sqrt x₂| = Real.sqrt ((Real.sqrt x₁ - Real.sqrt x₂) ^2) := by 
      rw [Real.sqrt_sq_eq_abs]
    rw [h16]
    rw [h15]
    all_goals norm_num 
  exact h18