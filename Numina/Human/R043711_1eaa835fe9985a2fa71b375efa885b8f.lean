import Mathlib
/-Solve the equation
3 * Real.sqrt (6 * x ^ 2 + 13 * x + 5) - 6 * Real.sqrt (2 * x + 1) - Real.sqrt (3 * x + 5) + 2 = 0
-/
theorem algebra_260323 (x : ℝ) (hx : 2 * x + 1 ≥ 0 ∧ 3 * x + 5 ≥ 0) :
    3 * Real.sqrt (6 * x ^ 2 + 13 * x + 5) - 6 * Real.sqrt (2 * x + 1) - Real.sqrt (3 * x + 5) + 2 = 0 ↔
    x = -1 / 3 ∨ x = -4 / 9 := by
  constructor
  · -- Forward direction: equation implies x = -1/3 or x = -4/9
    intro h
    have h1 : 2 * x + 1 ≥ 0 := hx.left
    have h2 : 3 * x + 5 ≥ 0 := hx.right
    have h3 : Real.sqrt (6 * x ^ 2 + 13 * x + 5) ≥ 0 := Real.sqrt_nonneg (6 * x ^ 2 + 13 * x + 5)
    have h4 : Real.sqrt (2 * x + 1) ≥ 0 := Real.sqrt_nonneg (2 * x + 1)
    have h5 : Real.sqrt (3 * x + 5) ≥ 0 := Real.sqrt_nonneg (3 * x + 5)
    have h6 : 3 * Real.sqrt (6 * x ^ 2 + 13 * x + 5) - 6 * Real.sqrt (2 * x + 1) - Real.sqrt (3 * x + 5) + 2 = 0 := by linarith
    have h7 : Real.sqrt (6 * x ^ 2 + 13 * x + 5) = Real.sqrt (2 * x + 1) * Real.sqrt (3 * x + 5) := by
      have hmul : (2 * x + 1) * (3 * x + 5) = 6 * x^2 + 13 * x + 5 := by ring
      rw [←hmul]
      rw [Real.sqrt_mul]
      all_goals linarith
    rw [h7] at h6
    have h8 : 3 * Real.sqrt (2 * x + 1) * Real.sqrt (3 * x + 5) - 6 * Real.sqrt (2 * x + 1) - Real.sqrt (3 * x + 5) + 2 = 0 := by linarith
    have h9 : (Real.sqrt (3 * x + 5) = 2) ∨ (Real.sqrt (2 * x + 1) = 1 / 3) := by
      by_cases hcase : Real.sqrt (3 * x + 5) = 2
      · left
        exact hcase
      · right
        have h_ne : Real.sqrt (3 * x + 5) ≠ 2 := by
          intro h
          exact hcase h
        have h10 : Real.sqrt (2 * x + 1) = 1 / 3 := by
          have h11 : 3 * Real.sqrt (3 * x + 5) - 6 ≠ 0 := by
            intro h
            have : Real.sqrt (3 * x + 5) = 2 := by
              linarith
            exact h_ne this
          have h12 : Real.sqrt (2 * x + 1) = (Real.sqrt (3 * x + 5) - 2) / (3 * Real.sqrt (3 * x + 5) - 6) := by
            field_simp [h11]
            nlinarith [h8, Real.sqrt_nonneg (2 * x + 1), Real.sqrt_nonneg (3 * x + 5)]
          have h13 : (Real.sqrt (3 * x + 5) - 2) / (3 * Real.sqrt (3 * x + 5) - 6) = 1 / 3 := by
            have h14 : 3 * Real.sqrt (3 * x + 5) - 6 ≠ 0 := h11
            field_simp [h14]
            nlinarith [Real.sqrt_nonneg (3 * x + 5)]
          rw [h12, h13]
        linarith [h10, Real.sqrt_nonneg (2 * x + 1)]
    cases h9 with
    | inl hcase1 =>
      have hx1 : 3 * x + 5 = 4 := by
        have hsq : (Real.sqrt (3 * x + 5)) ^ 2 = 4 := by
          rw [hcase1]
          norm_num
        rw [Real.sq_sqrt (by linarith)] at hsq
        linarith
      have hx2 : x = -1 / 3 := by linarith
      left
      exact hx2
    | inr hcase2 =>
      have hx1 : 2 * x + 1 = (1 / 3) ^ 2 := by
        have hsq : (Real.sqrt (2 * x + 1)) ^ 2 = (1 / 3) ^ 2 := by
          rw [hcase2]
        rw [Real.sq_sqrt (by linarith)] at hsq
        linarith
      have hx2 : x = -4 / 9 := by
        nlinarith
      right
      exact hx2
  · -- Backward direction: x = -1/3 or x = -4/9 implies equation holds
    rintro (h | h)
    · -- x = -1/3
      rw [h]
      have h1 : Real.sqrt (6 * (-1 / 3 : ℝ) ^ 2 + 13 * (-1 / 3) + 5) = 2 / Real.sqrt 3 := by
        rw [show (6 * (-1 / 3 : ℝ) ^ 2 + 13 * (-1 / 3) + 5 : ℝ) = 4 / 3 by norm_num]
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      have h2 : Real.sqrt (2 * (-1 / 3 : ℝ) + 1) = 1 / Real.sqrt 3 := by
        rw [show (2 * (-1 / 3 : ℝ) + 1 : ℝ) = (1 / 3 : ℝ) by norm_num]
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
      have h3 : Real.sqrt (3 * (-1 / 3 : ℝ) + 5) = 2 := by
        rw [show (3 * (-1 / 3 : ℝ) + 5 : ℝ) = (4 : ℝ) by norm_num]
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
      rw [h1, h2, h3]
      field_simp
      ring_nf
    · -- x = -4/9
      rw [h]
      have h1 : Real.sqrt (6 * (-4 / 9 : ℝ) ^ 2 + 13 * (-4 / 9) + 5) = Real.sqrt 11 / (3 * Real.sqrt 3) := by
        have h11 : (6 * (-4 / 9 : ℝ) ^ 2 + 13 * (-4 / 9) + 5 : ℝ) = 11 / 27 := by norm_num
        rw [h11]
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      have h2 : Real.sqrt (2 * (-4 / 9 : ℝ) + 1) = 1 / 3 := by
        rw [show (2 * (-4 / 9 : ℝ) + 1 : ℝ) = (1 / 9 : ℝ) by norm_num]
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
      have h3 : Real.sqrt (3 * (-4 / 9 : ℝ) + 5) = Real.sqrt 11 / Real.sqrt 3 := by
        have h31 : (3 * (-4 / 9 : ℝ) + 5 : ℝ) = 11 / 3 := by norm_num
        rw [h31]
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h1, h2, h3]
      field_simp
      linarith