import Mathlib

theorem algebra_228784 {a b : ℝ} (h₀ : a^2 + b^2 = 7 * a * b) (h₁ : a * b ≠ 0) :
    Real.log |(a + b) / 3| = (Real.log |a| + Real.log |b|) / 2 := by
  have h2 : a * b ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_pos_of_ne_zero h₁]

  have h4 : (a + b) ^ 2 = 9 * (a * b) := by
    nlinarith [h₀, sq_nonneg (a - b)]

  have h6 : |(a + b) / 3| ^ 2 = a * b := by 
    calc 
      |(a + b) / 3| ^ 2 = ((a + b) / 3) ^ 2 := by 
        rw [sq_abs]
      _ = (a + b) ^ 2 / 9 := by
        ring_nf
      _ = 9 * (a * b) / 9 := by
        rw [h4]
      _ = a * b := by
        field_simp

  have ha1 : a ≠ 0 := by
    by_contra h
    have h2 : a * b = 0 := by
      rw [h]
      norm_num
    contradiction

  have hb1 : b ≠ 0 := by
    by_contra h
    have h2 : a * b = 0 := by
      rw [h]
      norm_num
    contradiction
  
  have ha2 : |a| ≠ 0 := by
    by_contra h
    have h3 : a = 0 := by
      simpa [abs_eq_zero] using h
    contradiction
  
  have hb2 : |b| ≠ 0 := by
    by_contra h
    have h3 : b = 0 := by
      simpa [abs_eq_zero] using h
    contradiction
  
  have h11 : 2 * Real.log |(a + b) / 3| = Real.log |a| + Real.log |b| := by
    calc 
      2 * Real.log |(a + b) / 3| = Real.log (|(a + b) / 3| ^ 2) := by 
        simp [Real.log_pow]
        <;> ring_nf
      _ = Real.log (a * b) := by 
        rw [show |(a + b) / 3| ^ 2 = a * b by linarith [h6]]
      _ = Real.log |a| + Real.log |b| := by
        have hab : a * b = |a| * |b| := by
          have hab_nonneg : a * b ≥ 0 := h2
          have : |a| * |b| = |a * b| := by 
            simp [abs_mul]
          have h3 : |a * b| = a * b := by
            rw [abs_of_nonneg hab_nonneg]
          linarith
        rw [hab]
        rw [Real.log_mul (by 
          exact_mod_cast ha2
        ) (by 
          exact_mod_cast hb2
        )]

  linarith