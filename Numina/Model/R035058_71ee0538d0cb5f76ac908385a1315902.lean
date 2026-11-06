import Mathlib

theorem algebra_627053 {x y : ℝ}
  (h₀ : x + y = 4) (h₁ : x * y = -4) :
  (x ^ 3 + y ^ 3) / (x ^ 3 - y ^ 3) = 7 * √2 / 10 ∨ (x ^ 3 + y ^ 3) / (x ^ 3 - y ^ 3) = - 7 * √2 / 10 := by

  have h2 : x ^ 3 + y ^ 3 = 112 := by
    calc
      x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by ring
      _ = 4 ^ 3 - 3 * (-4) * 4 := by rw [h₀, h₁]
      _ = 64 + 48 := by norm_num
      _ = 112 := by norm_num

  have h3 : (x - y) ^ 2 = 32 := by
    nlinarith
  have h5 : x ^ 2 + x * y + y ^ 2 = 20 := by
    nlinarith [show x ^ 2 + y ^ 2 = 24 from by nlinarith [h₀, h₁], h₁]

  have h6 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by
    ring

  have h7 : x ^ 3 - y ^ 3 = (x - y) * 20 := by
    rw [h6]
    nlinarith [h5]

  have h32sqrt : Real.sqrt 32 = 4 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h11 : (x - y) = Real.sqrt 32 ∨ (x - y) = -Real.sqrt 32 := by
    apply eq_or_eq_neg_of_sq_eq_sq
    field_simp
    nlinarith
  rcases h11 with h11 | h11
  · -- Let $ x - y = \sqrt{32} $
    have h12 : (x - y) = 4 * Real.sqrt 2 := by
      rw [h11]
      nlinarith [h32sqrt]
    have h13 : x ^ 3 - y ^ 3 = 80 * Real.sqrt 2 := by
      rw [h7]
      rw [h12]
      nlinarith
    have h14 : (x ^ 3 + y ^ 3) / (x ^ 3 - y ^ 3) = 7 * Real.sqrt 2 / 10 := by
      rw [show x ^ 3 + y ^ 3 = 112 by linarith [h2], h13]
      have h16 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      field_simp [(show (80 * Real.sqrt 2 : ℝ) ≠ 0 by
        have h16 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
        have hne : (80 * Real.sqrt 2 : ℝ) ≠ 0 := by
          intro h'
          have h20 : Real.sqrt 2 = 0 := by
            nlinarith
          linarith [h16, h20]
        assumption
      )]
      <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
    have h17 : (x ^ 3 + y ^ 3) / (x ^ 3 - y ^ 3) = 7 * √2 / 10 := by
      nlinarith [h14, Real.sqrt_nonneg 2]
    left
    linarith [h17]
  · -- Let $ x - y = - \sqrt{32} $
    have h12 : (x - y) = -4 * Real.sqrt 2 := by
      rw [h11]
      nlinarith [h32sqrt]
    have h13 : x ^ 3 - y ^ 3 = -80 * Real.sqrt 2 := by
      rw [h7]
      rw [h12]
      nlinarith
    have h15 : (x ^ 3 + y ^ 3) / (x ^ 3 - y ^ 3) = -7 * Real.sqrt 2 / 10 := by
      rw [show x ^ 3 + y ^ 3 = 112 by linarith [h2], h13]
      have h16 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h17 : (112 : ℝ) / (-80 * Real.sqrt 2) = -7 * Real.sqrt 2 / 10 := by
        field_simp [(show (-80 * Real.sqrt 2 : ℝ) ≠ 0 by
          have h16 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
          have hne : (-80 * Real.sqrt 2 : ℝ) ≠ 0 := by
            intro h'
            have h20 : Real.sqrt 2 = 0 := by
              nlinarith
            linarith [h16, h20]
          assumption
        )]
        <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (2 : ℝ), h16]
      linarith [h17, Real.sqrt_nonneg 2]
    have h17 : (x ^ 3 + y ^ 3) / (x ^ 3 - y ^ 3) = -7 * √2 / 10 := by
      nlinarith [h15, Real.sqrt_nonneg 2]
    right
    linarith [h17]