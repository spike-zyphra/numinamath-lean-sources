import Mathlib


theorem algebra_208231 :
  { x : ℝ |
    ∃ a b c d : ℝ,
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧
      a / b + b / c + c / d + d / a = 6 ∧
      a / c + b / d + c / a + d / b = 8 ∧
      x = a / b + c / d }
  = { 2, 4 } := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x ∈ left side, prove x ∈ {2, 4}
    rintro ⟨a, b, c, d, ha, hb, hc, hd, h1, h2, h3⟩
    have eq1 : a / b + b / c + c / d + d / a = 6 := h1
    have eq2 : a / c + b / d + c / a + d / b = 8 := h2
    have h4 : x = a / b + c / d := h3
    have eq3 : a / b + c / d + (b / c + d / a) = 6 := by linarith
    have eq4 : (a / b + c / d) * (b / c + d / a) = 8 := by
      have eq3' : (a / b + c / d) * (b / c + d / a) = a / c + b / d + c / a + d / b := by
        field_simp [hb, hc, ha, hd]
        <;> nlinarith
      rw [eq3']
      linarith
    have h7 : (a / b + c / d) ^ 2 - 6 * (a / b + c / d) + 8 = 0 := by
      have eq8 : (a / b + c / d) + (b / c + d / a) = 6 := by linarith
      have eq9 : (a / b + c / d) * (b / c + d / a) = 8 := by linarith
      nlinarith [sq_nonneg ((a / b + c / d) - 2), sq_nonneg ((b / c + d / a) - 2)]
    have h8 : (a / b + c / d - 2) * (a / b + c / d - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- a / b + c / d - 2 = 0, so a / b + c / d = 2
      have h11 : x = 2 := by
        nlinarith [h4, h9]
      left
      linarith
    · -- a / b + c / d - 4 = 0, so a / b + c / d = 4
      have h11 : x = 4 := by
        nlinarith [h4, h10]
      right
      linarith
  · -- Assume x ∈ {2, 4}, prove x ∈ left side
    rintro (rfl | rfl)
    · -- x = 2
      use 1, (2 + Real.sqrt 2), 1, (2 - Real.sqrt 2)
      constructor
      · -- a ≠ 0
        norm_num
      constructor
      · -- b ≠ 0
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      constructor
      · -- c ≠ 0
        norm_num
      constructor
      · -- d ≠ 0
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      constructor
      · -- a / b + b / c + c / d + d / a = 6
        field_simp [(show (2 + Real.sqrt 2 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]), (show (2 - Real.sqrt 2 : ℝ) ≠ 0 by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))])]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
      constructor
      · -- a / c + b / d + c / a + d / b = 8
        field_simp [(show (2 + Real.sqrt 2 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]), (show (2 - Real.sqrt 2 : ℝ) ≠ 0 by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))])]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
      · -- x = a / b + c / d
        field_simp [(show (2 + Real.sqrt 2 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]), (show (2 - Real.sqrt 2 : ℝ) ≠ 0 by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))])]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
    · -- x = 4
      use (2 + Real.sqrt 2), (1 : ℝ), (2 - Real.sqrt 2), (1 : ℝ)
      constructor
      · -- a ≠ 0
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      constructor
      · -- b ≠ 0
        norm_num
      constructor
      · -- c ≠ 0
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      constructor
      · -- d ≠ 0
        norm_num
      constructor
      · -- a / b + b / c + c / d + d / a = 6
        field_simp [(show (2 - Real.sqrt 2 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]), (show (2 + Real.sqrt 2 : ℝ) ≠ 0 by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))])]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
      constructor
      · -- a / c + b / d + c / a + d / b = 8
        field_simp [(show (2 - Real.sqrt 2 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]), (show (2 + Real.sqrt 2 : ℝ) ≠ 0 by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))])]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
      · -- x = a / b + c / d
        field_simp [(show (2 - Real.sqrt 2 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]), (show (2 + Real.sqrt 2 : ℝ) ≠ 0 by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))])]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]