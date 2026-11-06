import Mathlib
open Real
theorem algebra_187131 : {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 4 = 5 ∧ x * y ^ 2 = 2} = {(2, 1), (2, -1), (1, √2), (1, -√2)}:= by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x^2 + y^4 = 5 ∧ x * y^2 = 2), prove * is one of the four solutions.
    rintro ⟨h1, h2⟩
    have h3 : x ^ 2 * y ^ 4 = 4:= by
      nlinarith
    have h5 : (y ^ 4) = 1 ∨ (y ^ 4) = 4 := by
      have h11 : x ^ 2 = 5 - y ^ 4 := by linarith
      rw [h11] at h3
      have h99 : (y ^ 4 - 1) * (y ^ 4 - 4) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h99) with h10 h11
      · -- Case y^4-1 =0, so y^4=1
        left
        linarith
      · -- Case y^4 -4=0, so y^4=4
        right
        linarith
    cases h5 with
    | inl h6 =>
      have h7 : y ^ 2 = 1 := by nlinarith [sq_nonneg (y ^ 2 - 1)]
      have h8 : x = 2 := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (y ^ 2 - 1)]
      have hy1 : y = 1 ∨ y = -1 := by
        have h9 : y ^ 2 = 1 := h7
        have : y = 1 ∨ y = -1 := by
          rw [sq_eq_one_iff] at h9
          tauto
        tauto
      rcases hy1 with (h9 | h9)
      · -- Case y = 1
        simp [h8, h9]
      · -- Case y = -1
        simp [h8, h9]
    | inr h6 =>
      have h7 : y ^ 2 = 2 := by nlinarith [sq_nonneg (y ^ 2 - 2)]
      have h8 : x = 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y ^ 2 - 2)]
      have hy1 : y = Real.sqrt 2 ∨ y = -Real.sqrt 2 := by
        have h9 : y ^ 2 = 2 := h7
        have h10 : y ^ 2 - 2 = 0 := by linarith
        have h11 : (y - Real.sqrt 2) * (y + Real.sqrt 2) = 0 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h11) with h12 h13
        · -- Case y - Real.sqrt 2 = 0
          left
          linarith
        · -- Case y + Real.sqrt 2 = 0
          right
          linarith
      rcases hy1 with (h9 | h9)
      · -- Case y = Real.sqrt 2
        simp [h8, h9]
      · -- Case y = -Real.sqrt 2
        simp [h8, h9]
  · -- Show that the four solutions satisfy both equations.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (2, 1)
      constructor <;> norm_num
    · -- Check (2, -1)
      constructor <;> norm_num
    · -- Check (1, √2)
      constructor
      · -- Check x^2 + y^4 = 5
        have h1' : (1 : ℝ) ^ 2 + (Real.sqrt (2 : ℝ)) ^ 4 = 5 := by
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), pow_two_nonneg (Real.sqrt 2 - 2 : ℝ)]
        exact h1'
      · -- Check x * y^2 = 2
        have h2' : (1 : ℝ) * (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        exact h2'
    · -- Check (1, -√2)
      constructor
      · -- Check x^2 + y^4 = 5
        have h1' : (1 : ℝ) ^ 2 + (-Real.sqrt (2 : ℝ)) ^ 4 = 5 := by
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), pow_two_nonneg (Real.sqrt 2 - 2 : ℝ)]
        exact h1'
      · -- Check x * y^2 = 2
        have h2' : (1 : ℝ) * (-Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        exact h2'