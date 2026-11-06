import Mathlib

theorem algebra_95119 {p : ℝ} (r₁ r₂ : ℝ) (h₁ : r₁ ≠ r₂)
    (h₂ : r₁^2 + p * r₁ + 8 = 0) (h₃ : r₂^2 + p * r₂ + 8 = 0) :
    |r₁ + r₂| > 4 * Real.sqrt 2 := by 
  have eq1 : r₁^2 + p * r₁ + 8 - (r₂^2 + p * r₂ + 8) = 0 := by linarith
  have eq2 : (r₁ - r₂) * (r₁ + r₂ + p) = 0 := by 
    nlinarith 
  have hp : r₁ + r₂ + p = 0 := by 
    apply (mul_left_inj' (show r₁ - r₂ ≠ 0 by 
      intro h
      apply h₁
      linarith
    )).mp 
    linarith
  have h4 : (r₁ - r₂) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero
    intro h
    apply h₁
    linarith
  have h6 : r₁ * r₂ = 8 := by
    nlinarith [sq_pos_of_ne_zero (show (r₁ - r₂) ≠ 0 by
      intro h
      apply h₁
      linarith
    ), sq_nonneg (r₁ - r₂)]
  have h7 : (r₁ + r₂) ^ 2 > 32 := by 
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < 1 by norm_num), sq_nonneg (r₁ - r₂)]
  have h8 : |r₁ + r₂| = Real.sqrt ((r₁ + r₂) ^ 2) := by 
    rw [Real.sqrt_sq_eq_abs]
    <;> norm_num 
  have h9 : 4 * Real.sqrt 2 = Real.sqrt 32 := by 
    have h10 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    linarith [h10]
  have h10 : |r₁ + r₂| ^ 2 > 32 := by 
    have h11 : |r₁ + r₂| = Real.sqrt ((r₁ + r₂) ^ 2) := by 
      rw [Real.sqrt_sq_eq_abs]
      <;> norm_num 
    have h13 : |r₁ + r₂| ^ 2 = (r₁ + r₂) ^ 2 := by 
      calc
        |r₁ + r₂| ^ 2 = (Real.sqrt ((r₁ + r₂) ^ 2)) ^ 2 := by rw [h11]
        _ = (r₁ + r₂) ^ 2 := by rw [Real.sq_sqrt (by nlinarith [sq_nonneg (r₁ + r₂)])]
    nlinarith [h13, h7]
  have h11 : (4 * Real.sqrt 2) ^ 2 = (32 : ℝ) := by 
    calc
      (4 * Real.sqrt 2) ^ 2 = 16 * (Real.sqrt 2) ^ 2 := by ring
      _ = 16 * (2 : ℝ) := by rw [Real.sq_sqrt]; positivity
      _ = 32 := by norm_num
  have h12 : |r₁ + r₂| > 4 * Real.sqrt 2 := by
    nlinarith [abs_nonneg (r₁ + r₂), Real.sqrt_nonneg 2, Real.sqrt_nonneg 32, Real.sqrt_nonneg ((r₁ + r₂) ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ ((r₁ + r₂) ^ 2 : ℝ) by nlinarith [sq_nonneg (r₁ + r₂)])]
  linarith [h12]