import Mathlib

theorem algebra_284982 (a b : ℤ) (h : ∃ x, x^2 + a * x + b = 0 ∧ x = Real.sqrt (7 - 4 * Real.sqrt 3)) :
    b - a = 5 := by
  rcases h with ⟨x, hx1, hx⟩
  have h1 : (↑x : ℝ) = Real.sqrt (7 - 4 * Real.sqrt 3) := by
    exact_mod_cast hx
  have h2 : Real.sqrt (7 - 4 * Real.sqrt 3) = 2 - Real.sqrt 3 := by
    have h3 : Real.sqrt (7 - 4 * Real.sqrt 3) = 2 - Real.sqrt 3 := by
      have h4 : (2 - Real.sqrt 3) ^ 2 = (7 - 4 * Real.sqrt 3 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h5 : 2 - Real.sqrt 3 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (3 : ℝ) ≥ (1 : ℝ) by norm_num)]
      rw [← h4]
      field_simp [Real.sqrt_sq (show (2 - Real.sqrt 3 : ℝ) ≥ 0 by linarith)]
    exact h3
  have h3 : (↑x : ℝ) = (2 - Real.sqrt 3 : ℝ) := by
    rw [h2] at h1
    linarith
  have h12 : Real.sqrt 3 > (1 : ℝ) := by
    have h13 : Real.sqrt 3 > Real.sqrt 1 := by
      apply Real.sqrt_lt_sqrt
      all_goals
        norm_num
    have h13' : Real.sqrt 1 = (1 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    nlinarith [h13', h13, Real.sqrt_nonneg 3]
  have h13 : Real.sqrt 3 < (2 : ℝ) := by
    have h15 : Real.sqrt 3 < (2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ)]
    linarith
  have h14 : (2 - Real.sqrt 3 : ℝ) > (0 : ℝ) := by
    have h15 : Real.sqrt 3 < (2 : ℝ) := h13
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have h15 : (2 - Real.sqrt 3 : ℝ) < (1 : ℝ) := by
    have h19 : Real.sqrt 3 > (1 : ℝ) := h12
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  -- Now we have `0 < (↑x : ℝ) < 1`.
  -- Since `x` is an integer, this implies `↑x = 0` can't be.
  have h16 : x > 0 := by
    by_contra h
    push_neg at h
    have h21 : x ≤ 0 := by omega
    have h21' : (↑x : ℝ) ≤ (0 : ℝ) := by
      exact_mod_cast h21
    nlinarith
  have h17 : x < 1 := by
    have h19 : (↑x : ℝ) < (1 : ℝ) := by
      nlinarith [h3, h15]
    have h19' : x < 1 := by
      by_contra h
      push_neg at h
      have h20 : x ≥ 1 := by omega
      have h21 : (↑x : ℝ) ≥ (1 : ℝ) := by
        exact_mod_cast h20
      nlinarith
    omega
  -- Hence inconsistencies since x is an integer with 0 < x < 1
  omega