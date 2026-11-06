import Mathlib

/- $a$ and $b$ are integers such that $a+\sqrt{b}=\sqrt{15+\sqrt{216}}$. Compute $a / b$.-/
theorem algebra_611145 (a b : ℤ) (hb : 0 ≤ b) (h : a + Real.sqrt b = Real.sqrt (15 + Real.sqrt 216)) : (a / b : ℚ) = 1 / 2 := by
  -- Square both sides of the hypothesis.
  have h₁ := congr_arg (· ^ 2) h
  simp [add_sq] at h₁
  repeat rw [Real.sq_sqrt (by positivity)] at h₁
  -- Consider cases where 0 ≤ a and a < 0 respectively.
  by_cases ha : 0 ≤ a
  . -- Rearrange the equation.
    replace h₁ : (a ^ 2 + b - 15) + 2 * Real.sqrt (a ^ 2 * b) = Real.sqrt 216 := by
      field_simp
      linarith only [h₁]
    -- Show that a² + b - 15 = 0.
    have h₂ : (a ^ 2 + b - 15 : ℝ) = 0 := by
      -- Assume on the contrary that a² + b - 15 ≠ 0.
      by_contra! h₂
      -- Square both sides and note that a²b has to be a perfect square.
      have h₃ := congr_arg (· ^ 2) h₁
      simp at h₃
      rw [add_sq, mul_pow, Real.sq_sqrt (by positivity)] at h₃
      -- We show this by noting that √(a²b) is rational.
      have h₄ : ¬Irrational (Real.sqrt (a ^ 2 * b)) := by
        simp only [Irrational]
        simp
        use (216 - (a ^ 2 + b - 15) ^ 2 - 2 ^ 2 * (a ^ 2 * b)) / (4 * (a ^ 2 + b - 15))
        field_simp at h₃ ⊢
        linarith only [h₃]
      norm_cast at h₄
      rw [irrational_sqrt_intCast_iff_of_nonneg (by positivity), not_not] at h₄
      obtain ⟨k, h₄⟩ := h₄
      rify at h₄
      rw [h₄, Real.sqrt_mul_self_eq_abs] at h₁
      -- But it means that √216 has to be rational, which is absurd.
      have h₅ : ¬Irrational (Real.sqrt 216) := by
        simp only [Irrational]
        simp
        use a ^ 2 + b - 15 + 2 * |k|
        field_simp [h₁]
      rw [show (216 : ℝ) = (216 : ℕ) by simp] at h₅
      rw [irrational_sqrt_natCast_iff, not_not] at h₅
      obtain ⟨m, h₅⟩ := h₅
      linarith only [show 14 < m by nlinarith, show m < 15 by nlinarith]
    simp [h₂] at h₁
    -- Square both sides to get a²b = 54.
    replace h₁ := congr_arg (· ^ 2) h₁
    field_simp [mul_pow] at h₁
    -- Now a² + b = 15 = 9 + 6 and a²b = 54 = 9 * 6, we shall prove that (a², b) = (9, 6) or (6, 9).
    have h₃ : ((b - 6) * (b - 9) : ℝ) = 0 := by
      nlinarith
    norm_cast at h₃
    simp at h₃
    -- Prove b ≠ 9 by contradiction, since otherwise √b is rational.
    have h₄ : b - 9 ≠ 0 := by
      by_contra! h₄
      field_simp [eq_of_sub_eq_zero h₄, show (9 : ℝ) = 3 ^ 2 by norm_num] at h
      have h₅ : ¬Irrational ((15 : ℤ) + Real.sqrt 216) := by
        simp only [Irrational]
        simp
        use (a + 3) ^ 2
        field_simp [h]
      -- We get 216 being a square, which is absurd.
      rw [add_comm, irrational_add_int_iff, show (216 : ℝ) = (216 : ℕ) by simp] at h₅
      rw [irrational_sqrt_natCast_iff, not_not] at h₅
      obtain ⟨m, h₅⟩ := h₅
      linarith only [show 14 < m by nlinarith, show m < 15 by nlinarith]
    simp [h₄] at h₃
    -- We get b = 6.
    apply eq_of_sub_eq_zero at h₃
    replace h₁ : (a ^ 2 : ℝ) = 3 ^ 2 := by
      simp [h₃] at h₁
      linarith
    -- We get a = 3, which closes the goal.
    rw [sq_eq_sq₀ (by simp [ha]) (by norm_num)] at h₁
    norm_cast at h₁
    norm_num [h₁, h₃]
  . -- Rearrange the equation.
    replace h₁ : (a ^ 2 + b - 15) - 2 * Real.sqrt ((-a) ^ 2 * b) = Real.sqrt 216 := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by simp; linarith)]
      linarith only [h₁]
    -- Show that a² + b - 15 = 0.
    have h₂ : (a ^ 2 + b - 15 : ℝ) = 0 := by
      -- Assume on the contrary that a² + b - 15 ≠ 0.
      by_contra! h₂
      -- Square both sides and note that a²b has to be a perfect square.
      have h₃ := congr_arg (· ^ 2) h₁
      simp at h₃
      rw [sub_sq, mul_pow, Real.sq_sqrt (by positivity)] at h₃
      -- We show this by noting that √(a²b) is rational.
      have h₄ : ¬Irrational (Real.sqrt (a ^ 2 * b)) := by
        simp only [Irrational]
        simp
        use (216 - (a ^ 2 + b - 15) ^ 2 - 2 ^ 2 * (a ^ 2 * b)) / (-4 * (a ^ 2 + b - 15))
        field_simp at h₃ ⊢
        linarith only [h₃]
      norm_cast at h₄
      rw [irrational_sqrt_intCast_iff_of_nonneg (by positivity), not_not] at h₄
      obtain ⟨k, h₄⟩ := h₄
      rify at h₄
      rw [<-neg_sq] at h₄
      rw [h₄, Real.sqrt_mul_self_eq_abs] at h₁
      -- But it means that √216 has to be rational, which is absurd.
      have h₅ : ¬Irrational (Real.sqrt 216) := by
        simp only [Irrational]
        simp
        use a ^ 2 + b - 15 - 2 * |k|
        field_simp [h₁]
      rw [show (216 : ℝ) = (216 : ℕ) by simp] at h₅
      rw [irrational_sqrt_natCast_iff, not_not] at h₅
      obtain ⟨m, h₅⟩ := h₅
      linarith only [show 14 < m by nlinarith, show m < 15 by nlinarith]
    -- This is a contradiction, since it means that √216 < 0.
    simp [h₂] at h₁
    linarith only [h₁, show Real.sqrt (a ^ 2 * b) ≥ 0 by positivity, show Real.sqrt 216 > 0 by positivity]
