import Mathlib

theorem algebra_108375 (a : ℝ) :
    (∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1 > 1 ∧ x2 > 1 ∧ a * x1^2 - (a + 2) * x1 + (a + 1) = 0 ∧
      a * x2^2 - (a + 2) * x2 + (a + 1) = 0) ↔ a ∈ Set.Ioo 1 (2 / Real.sqrt 3) := by
  constructor
  · -- Forward direction: existence of two distinct roots implies parameters
    rintro ⟨x1, x2, hx12, hx1, hx2, h1, h2⟩
    have h_sub : a * (x1^2 - x2^2) - (a + 2) * (x1 - x2) = 0 := by
      nlinarith
    have h_eq : a * (x1 + x2) - (a + 2) = 0 := by
      apply (mul_left_inj' (show x1 - x2 ≠ 0 by 
        intro h'
        apply hx12
        linarith
      )).mp
      linarith [h_sub]
    have ha1 : a > 0 := by
      nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by
        intro h
        apply hx12
        linarith
      ), sq_nonneg (x1 - 1), sq_nonneg (x2 - 1), sq_nonneg (x1 + x2 - 2)]
    have ha2 : a > 1 := by
      nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by 
        intro h
        apply hx12
        linarith
      ), sq_nonneg (x1 - 1), sq_nonneg (x2 - 1), sq_nonneg (x1 - x2), sq_nonneg (a * (x1 - x2)), h1, h2]
    have ha3 : a ^ 2 < 4 / 3 := by
      have h4 : (a + 2) ^ 2 - 4 * a * (a + 1) > 0 := by
        nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by 
          intro h
          apply hx12
          linarith
        ), sq_nonneg (x1 - x2), sq_nonneg (a * (x1 - x2)), h1, h2]
      nlinarith
    constructor
    · -- Show a > 1
      linarith
    · -- Show a < 2 / Real.sqrt 3
      have h5 : Real.sqrt 3 > 0 := by
        positivity
      have h6 : a ^ 2 < 4 / 3 := ha3
      have h7 : a * Real.sqrt 3 < 2 := by
        have h8 : 0 < (Real.sqrt 3) := by
          positivity
        have h9 : a ^ 2 < 4 / 3 := h6
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (a * Real.sqrt 3 - 2), sq_nonneg (a + 2), sq_nonneg (a - 2 / Real.sqrt 3)]
      have h8 : Real.sqrt 3 > 0 := by
        positivity
      have h9 : a * Real.sqrt 3 < 2 := h7
      have h11 : a < (2 / Real.sqrt 3) := by
        have h10 : Real.sqrt 3 > 0 := h8
        apply (lt_div_iff₀ h10).mpr
        nlinarith
      exact h11
  · -- Backward direction: parameters imply existence of two distinct roots
    rintro ⟨ha1, ha2⟩
    have h3 : a ^ 2 < 4 / 3 := by
      have h4 : a < 2 / Real.sqrt 3 := by 
        simpa using ha2
      have h5 : Real.sqrt 3 > 0 := by
        positivity
      have h6 : a * Real.sqrt 3 < 2 := by
        have h8 : a < 2 / Real.sqrt 3 := h4
        have h9 : Real.sqrt 3 > 0 := h5
        have h10 : a * Real.sqrt 3 < 2 := by
          apply (lt_div_iff₀ h5).mp at h8
          nlinarith
        linarith
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h4 : (a + 2) ^ 2 - 4 * a * (a + 1) > 0 := by
      nlinarith [h3]
    use ( (a + 2) + Real.sqrt ((a + 2) ^ 2 - 4 * a * (a + 1)) ) / (2 * a),
      ( (a + 2) - Real.sqrt ((a + 2) ^ 2 - 4 * a * (a + 1)) ) / (2 * a)
    constructor
    · -- Show x1 ≠ x2
      by_contra h
      field_simp [(show a ≠ 0 by linarith)] at h
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (a + 2) ^ 2 - 4 * a * (a + 1) by nlinarith [h4]), Real.sq_sqrt (show (0 : ℝ) ≤ ((a + 2) ^ 2 - 4 * a * (a + 1) : ℝ) by nlinarith [h4])]
    constructor
    · -- Show x1 > 1
      have h6 : ( (a + 2) + Real.sqrt ((a + 2) ^ 2 - 4 * a * (a + 1)) ) / (2 * a) > 1 := by
        apply (lt_div_iff₀ (by linarith)).mpr
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (a + 2) ^ 2 - 4 * a * (a + 1) by nlinarith [h4]), Real.sq_sqrt (show (0 : ℝ) ≤ ((a + 2) ^ 2 - 4 * a * (a + 1) : ℝ) by nlinarith [h4]), sq_nonneg (a - 1)]
      linarith
    constructor
    · -- Show x2 > 1
      have h7 : ( (a + 2) - Real.sqrt ((a + 2) ^ 2 - 4 * a * (a + 1)) ) / (2 * a) > 1 := by
        apply (lt_div_iff₀ (by linarith)).mpr
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (a + 2) ^ 2 - 4 * a * (a + 1) by nlinarith [h4]), Real.sq_sqrt (show (0 : ℝ) ≤ ((a + 2) ^ 2 - 4 * a * (a + 1) : ℝ) by nlinarith [h4]), sq_nonneg (a - 1)]
      linarith
    constructor
    · -- Show a * x1^2 - (a + 2) * x1 + (a + 1) = 0
      field_simp [(show a ≠ 0 by linarith)]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (a + 2) ^ 2 - 4 * a * (a + 1) by nlinarith [h4]), Real.sq_sqrt (show (0 : ℝ) ≤ ((a + 2) ^ 2 - 4 * a * (a + 1) : ℝ) by nlinarith [h4])]
    · -- Show a * x2^2 - (a + 2) * x2 + (a + 1) = 0
      field_simp [(show a ≠ 0 by linarith)]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (a + 2) ^ 2 - 4 * a * (a + 1) by nlinarith [h4]), Real.sq_sqrt (show (0 : ℝ) ≤ ((a + 2) ^ 2 - 4 * a * (a + 1) : ℝ) by nlinarith [h4])]