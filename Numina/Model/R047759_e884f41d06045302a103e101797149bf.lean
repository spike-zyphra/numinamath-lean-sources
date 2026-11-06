import Mathlib


open Real


theorem algebra_227503 :
    {x : ℝ | x ≠ 5 ∧ x^2 + (5 * x / (x - 5))^2 = 11} = {(-1 + Real.sqrt 21) / 2, (-1 - Real.sqrt 21) / 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x ≠ 5 and x^2 + (5 * x / (x - 5))^2 = 11, prove x ∈ {(-1 + Real.sqrt 21) / 2, (-1 - Real.sqrt 21) / 2}
    intro h
    rcases h with ⟨hx1, h_eq⟩
    have h1 : x - 5 ≠ 0 := by
      intro h2
      apply hx1
      linarith
    have h2 : (x^2 + (5 * x / (x - 5))^2) * (x - 5) ^ 2 = 11 * (x - 5) ^ 2 := by
      rw [h_eq]
    have h3 : (x^2 + (5 * x / (x - 5))^2) * (x - 5) ^ 2 = x^2 * (x - 5) ^ 2 + 25 * x^2 := by
      have h3a : (5 * x / (x - 5))^2 * (x - 5) ^ 2 = 25 * x^2 := by
        have h3b : (5 * x / (x - 5))^2 * (x - 5) ^ 2 = (25 * x^2) / (x - 5) ^ 2 * (x - 5) ^ 2 := by
          field_simp [h1]
          <;> ring
        rw [h3b]
        have h3c : (25 * x^2) / (x - 5) ^ 2 * (x - 5) ^ 2 = 25 * x^2 := by
          field_simp [h1]
        linarith
      calc
        (x^2 + (5 * x / (x - 5))^2) * (x - 5) ^ 2 = x^2 * (x - 5) ^ 2 + (5 * x / (x - 5))^2 * (x - 5) ^ 2 := by ring
        _ = x^2 * (x - 5) ^ 2 + 25 * x^2 := by rw [h3a]
    rw [h3] at h2
    have h4 : x ^ 4 - 10 * x ^ 3 + 39 * x ^ 2 + 110 * x - 275 = 0 := by
      nlinarith
    have h5 : (x^2 + x - 5) * (x^2 - 11 * x + 55) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- When $x^2 + x - 5 = 0$
      have h8 : x^2 + x - 5 = 0 := by linarith
      have h10 : (x - (-1 + Real.sqrt 21) / 2) * (x - (-1 - Real.sqrt 21) / 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (21 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- When x = (-1 + Real.sqrt 21) / 2
        left
        linarith
      · -- When x = (-1 - Real.sqrt 21) / 2
        right
        linarith
    · -- When $x^2 - 11x + 55 = 0$
      have h8 : x^2 - 11 * x + 55 = 0 := by linarith
      nlinarith [sq_nonneg (x - 11 / 2), Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
  · -- Assume x ∈ {(-1 + Real.sqrt 21) / 2, (-1 - Real.sqrt 21) / 2}, prove x ≠ 5 and x^2 + (5 * x / (x - 5))^2 = 11
    rintro (h | h)
    · -- When x = (-1 + Real.sqrt 21) / 2
      constructor
      · -- Show x ≠ 5
        by_contra h1
        have h2 : Real.sqrt 21 = 11 := by
          nlinarith
        nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
      · -- Show x^2 + (5 * x / (x - 5))^2 = 11
        have h3 : x ^ 2 + (5 * x / (x - 5))^2 = 11 := by
          have h13 : x ^ 2 + x - 5 = 0 := by
            rw [h]
            nlinarith [Real.sqrt_pos.mpr (by norm_num : (21 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
          have h3a : (5 * x / (x - 5)) = (-(1 + Real.sqrt 21) / 2) := by
            have hx5 : x - 5 ≠ 0 := by
              by_contra h2
              have h3 : x = 5 := by linarith
              rw [h3] at h13
              nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
            have h4 : x = (-1 + Real.sqrt 21) / 2 := by linarith
            rw [h4]
            have h5 : ((-1 + Real.sqrt 21) / 2 : ℝ) - 5 = (-11 + Real.sqrt 21) / 2 := by
              linarith
            have h6 : (5 * ((-1 + Real.sqrt 21) / 2) : ℝ) = (-5 + 5 * Real.sqrt 21) / 2 := by
              linarith
            rw [h5, h6]
            have h7 : (-11 + Real.sqrt 21 : ℝ) ≠ 0 := by
              by_contra h8
              have h9 : Real.sqrt 21 = 11 := by
                nlinarith
              nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
            field_simp [h7]
            nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
          have h3b : (5 * x / (x - 5))^2 = (11 + Real.sqrt 21) / 2 := by
            rw [h3a]
            nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
          have h3c : x^2 = (11 - Real.sqrt 21) / 2 := by
            nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
          linarith [h3b, h3c]
        linarith
    · -- When x = (-1 - Real.sqrt 21) / 2
      constructor
      · -- Show x ≠ 5
        by_contra h1
        have h2 : Real.sqrt 21 = -11 := by
          nlinarith
        nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
      · -- Show x^2 + (5 * x / (x - 5))^2 = 11
        have h3 : x ^ 2 + (5 * x / (x - 5))^2 = 11 := by
          have h13 : x ^ 2 + x - 5 = 0 := by
            rw [h]
            nlinarith [Real.sqrt_pos.mpr (by norm_num : (21 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
          have h3a : (5 * x / (x - 5)) = ((Real.sqrt 21 - 1) / 2) := by
            have hx5 : x - 5 ≠ 0 := by
              by_contra h2
              have h3 : x = 5 := by linarith
              rw [h3] at h13
              nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
            have h4 : x = (-1 - Real.sqrt 21) / 2 := by linarith
            rw [h4]
            have h5 : ((-1 - Real.sqrt 21) / 2 : ℝ) - 5 = (-11 - Real.sqrt 21) / 2 := by
              linarith
            have h6 : (5 * ((-1 - Real.sqrt 21) / 2) : ℝ) = (-5 - 5 * Real.sqrt 21) / 2 := by
              linarith
            rw [h5, h6]
            have h7 : (-11 - Real.sqrt 21 : ℝ) ≠ 0 := by
              by_contra h8
              have h9 : Real.sqrt 21 = -11 := by
                nlinarith
              nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
            field_simp [h7]
            nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
          have h3b : (5 * x / (x - 5))^2 = (11 - Real.sqrt 21) / 2 := by
            rw [h3a]
            nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
          have h3c : x^2 = (11 + Real.sqrt 21) / 2 := by
            nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
          linarith [h3b, h3c]
        linarith