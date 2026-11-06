import Mathlib
open Real

theorem algebra_217051 :
  {(x, y) : ℝ × ℝ |  y^2 = x^3 - 3 * x^2 + 2 * x ∧ x^2 = y^3 - 3 * y^2 + 2 * y } = {(0, 0), (2 - sqrt 2, 2 - sqrt 2), (2 + sqrt 2, 2 + sqrt 2)} := by
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y) satisfies both equations.
    rintro ⟨h₁, h₂⟩
    have h3 : (y - x) * (y ^ 2 + x * y + x ^ 2 - 2 * y - 2 * x + 2) = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x * y - 2), sq_nonneg (x ^ 2 - y ^ 2)]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case where y - x = 0, so x = y
      have h4' : x = y := by linarith
      have h5 : x^3 - 4 * x^2 + 2 * x = 0 := by
        rw [show y = x by linarith [h4']] at h₁
        nlinarith
      have h6 : x * (x ^ 2 - 4 * x + 2) = 0 := by
        nlinarith
      have h7 : x = 0 ∨ x ^ 2 - 4 * x + 2 = 0 := by
        cases (mul_eq_zero.1 h6) with
        | inl h =>
          left
          linarith
        | inr h =>
          right
          linarith
      cases h7 with
      | inl hx1 =>
        have hy1 : y = 0 := by
          nlinarith [h4', hx1]
        left
        simp [hx1, hy1]
      | inr h7 =>
        have hx2 : x ^ 2 - 4 * x + 2 = 0 := by
          linarith
        have h8 : (x - (2 - Real.sqrt 2)) * (x - (2 + Real.sqrt 2)) = 0 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2), sq_nonneg (Real.sqrt 2 - 2)]
        cases (mul_eq_zero.1 h8) with
        | inl hx3 =>
          have h9 : x = 2 - Real.sqrt 2 := by
            linarith
          have h10 : y = 2 - Real.sqrt 2 := by
            nlinarith [h4', h9]
          right
          left
          simp [h9, h10]
        | inr hx4 =>
          have h11 : x = 2 + Real.sqrt 2 := by
            linarith
          have h12 : y = 2 + Real.sqrt 2 := by
            nlinarith [h4', h11]
          right
          right
          simp [h11, h12]
    · -- Case where y^2 + xy + x^2 - 2y - 2x + 2 = 0.
      exfalso
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x * y - 2), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_pos_of_pos (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that all the pairs in the right-hand side of the equality satisfy the equations.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (0, 0)
      constructor
      · -- Check the first equation.
        norm_num
      · -- Check the second equation.
        norm_num
    · -- (2 - sqrt 2, 2 - sqrt 2)
      constructor
      · -- Check the first equation.
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2), sq_nonneg (Real.sqrt 2 - 2)]
      · -- Check the second equation.
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2), sq_nonneg (Real.sqrt 2 - 2)]
    · -- (2 + sqrt 2, 2 + sqrt 2)
      constructor
      · -- Check the first equation.
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2), sq_nonneg (Real.sqrt 2 - 2)]
      · -- Check the second equation.
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2), sq_nonneg (Real.sqrt 2 - 2)]