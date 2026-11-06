import Mathlib

theorem algebra_187720 (x : ℝ) :
    Real.log (81 * (3^(x^2 - 8 * x)) ^ ((1 : ℝ) / 3)) = 0 ↔ x = 2 ∨ x = 6 := by
  constructor
  · -- Assume $\ln(81 \cdot (3^{x^2 - 8 * x})^{1/3}) = 0$, prove $x = 2 \lor x = 6$
    intro h
    have h1 : 81 * ((3 : ℝ) ^ (x^2 - 8 * x)) ^ ((1 : ℝ) / 3) = 1 := by
      have : (81 * ((3 : ℝ) ^ (x^2 - 8 * x)) ^ ((1 : ℝ) / 3)) = 1 := by
        calc
          81 * ((3 : ℝ) ^ (x^2 - 8 * x)) ^ ((1 : ℝ) / 3) = Real.exp (Real.log (81 * ((3 : ℝ) ^ (x^2 - 8 * x)) ^ ((1 : ℝ) / 3))) := by 
            rw [Real.exp_log]
            positivity
          _ = Real.exp (0 : ℝ) := by
            rw [h]
          _ = (1 : ℝ) := by
            norm_num
      linarith
    have h2 : (81 * ((3 : ℝ) ^ (x^2 - 8 * x)) ^ ((1 : ℝ) / 3) ) = 1 := h1
    have h3 : (81 * ((3 : ℝ) ^ (x^2 - 8 * x)) ^ ((1 : ℝ) / 3) ) = (3 : ℝ) ^ (4 + (x^2 - 8 * x) / 3 : ℝ) := by
      have h4 : (81 : ℝ) = (3 : ℝ) ^ (4 : ℝ) := by norm_num
      have h5 : ((3 : ℝ) ^ (x^2 - 8 * x)) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ ((x^2 - 8 * x) / 3 : ℝ) := by
        rw [← Real.rpow_mul]
        ring
        all_goals linarith [show (0 : ℝ) < (3 : ℝ) by norm_num]
      rw [h4, h5]
      rw [← Real.rpow_add]
      ring_nf
      all_goals norm_num
    have h4 : (3 : ℝ) ^ (4 + (x^2 - 8 * x) / 3 : ℝ) = 1 := by
      rw [←h3]
      linarith [h2]
    have h5 : (4 + (x^2 - 8 * x) / 3 : ℝ) = (0 : ℝ) := by
      apply_fun (Real.logb (3 : ℝ)) at h4
      have h6 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (4 + (x^2 - 8 * x) / 3 : ℝ)) = (4 + (x^2 - 8 * x) / 3 : ℝ) := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      have h7 : Real.logb (3 : ℝ) (1 : ℝ) = 0 := by 
        simp [Real.logb_one]
      rw [h6, h7] at h4
      linarith
    have h6 : (x^2 - 8 * x + 12 : ℝ) = 0 := by
      linarith
    have h7 : (x - 2 : ℝ) * (x - 6 : ℝ) = 0 := by 
      ring_nf at h6 ⊢
      linarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case x - 2 = 0, so x = 2
      left
      linarith
    · -- Case x - 6 = 0, so x = 6
      right
      linarith
  · -- Assume x = 2 ∨ x = 6, prove $\ln(81 \cdot (3^{x^2 - 8 * x}) ^ (1 / 3)) = 0$
    rintro (h | h)
    · -- Case x = 2
      rw [h]
      have : (81 * ((3 : ℝ) ^ ((2 : ℝ) ^ 2 - 8 * (2 : ℝ)) ) ^ ((1 : ℝ) / 3)) = 1 := by
        have h1 : ((3 : ℝ) ^ ((2 : ℝ) ^ 2 - 8 * (2 : ℝ)) ) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ (-4 : ℝ) := by 
          have h2 : (2 ^ 2 - 8 * (2 : ℝ)) = (-12 : ℝ) := by norm_num
          rw [h2]
          have h3 : ((3 : ℝ) ^ (-12 : ℝ)) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ (-12 * (1 / 3) : ℝ) := by
            rw [← Real.rpow_mul]
            ring
            all_goals norm_num
          rw [h3]
          norm_num
        rw [h1]
        norm_num
      rw [this]
      norm_num
    · -- Case x = 6
      rw [h]
      have : (81 * ((3 : ℝ) ^ ((6 : ℝ) ^ 2 - 8 * (6 : ℝ)) ) ^ ((1 : ℝ) / 3)) = 1 := by 
        have h1 : ((3 : ℝ) ^ ((6 : ℝ) ^ 2 - 8 * (6 : ℝ)) ) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ (-4 : ℝ) := by 
          have h2 : (6 ^ 2 - 8 * (6 : ℝ)) = (-12 : ℝ) := by norm_num
          rw [h2]
          have h3 : ((3 : ℝ) ^ (-12 : ℝ)) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ (-12 * (1 / 3) : ℝ) := by 
            rw [← Real.rpow_mul]
            ring
            all_goals norm_num
          rw [h3]
          norm_num
        rw [h1]
        norm_num
      rw [this]
      norm_num