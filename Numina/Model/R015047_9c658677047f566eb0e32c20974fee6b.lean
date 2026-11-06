import Mathlib

theorem algebra_177688 (x : ℝ) (hx : x ≠ -1) :
    x * (6 - x) / (x + 1) * ((6 - x) / (x + 1) + x) = 8 ↔
    x = 2 - Real.sqrt 2 ∨ x = 2 + Real.sqrt 2 := by
  constructor
  · -- Assume the left side, prove the right (equation to solutions)
    intro h
    have h1 : x * (6 - x) / (x + 1) * ((6 - x) / (x + 1) + x) = 8 := h
    have h2 : x + 1 ≠ 0 := by
      intro h3
      apply hx
      linarith
    have eq1 : x * (6 - x) * (x ^ 2 + 6) = 8 * (x + 1) ^ 2 := by 
      have eq2 : x * (6 - x) / (x + 1) * ((6 - x) / (x + 1) + x) = 
        x * (6 - x) / (x + 1) * ((6 - x + x * (x + 1)) / (x + 1)) := by
        have eq3 : (6 - x) / (x + 1) + x = (6 - x + x * (x + 1)) / (x + 1) := by
          field_simp [h2]
          <;> ring
        rw [eq3]
      rw [eq2] at h1 
      have eq4 : x * (6 - x) / (x + 1) * ((6 - x + x * (x + 1)) / (x + 1)) = 
        x * (6 - x) * (6 - x + x * (x + 1)) / ((x + 1) * (x + 1)) := by 
        field_simp [h2]
        <;> ring
      rw [eq4] at h1
      have eq5 : x * (6 - x) * (6 - x + x * (x + 1)) / ((x + 1) * (x + 1)) = 8 := h1 
      have eq6 : x * (6 - x) * (6 - x + x * (x + 1)) = 8 * ((x + 1) * (x + 1)) := by
        field_simp [(show x + 1 ≠ 0 by exact h2)] at eq5 ⊢
        <;> nlinarith
      have eq7 : 6 - x + x * (x + 1) = x ^ 2 + 6 := by
        nlinarith
      rw [eq7] at eq6
      nlinarith
    have eq3 : (x ^ 2 - 4 * x + 2) * (x ^ 2 - 2 * x + 4) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2 - 4 * x + 2), sq_nonneg (x ^ 2 - 2 * x + 4), sq_nonneg (x - 2), sq_nonneg (x), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    cases (mul_eq_zero.1 eq3) with 
    | inl h4 =>
      have h5 : (x - (2 - Real.sqrt 2)) * (x - (2 + Real.sqrt 2)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      cases (mul_eq_zero.1 h5) with 
      | inl h6 =>
        left
        linarith
      | inr h7 =>
        right
        linarith
    | inr h5 =>
      have h6 : x ^ 2 - 2 * x + 4 > 0 := by 
        nlinarith [sq_nonneg (x - 1), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      exfalso
      nlinarith [sq_nonneg (x - 1), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Assume the right side, prove the left (solutions to equation)
    rintro (h | h)
    · -- Case x = 2 - Real.sqrt 2 
      rw [h]
      have h2 : (2 - Real.sqrt 2 : ℝ) + 1 ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      field_simp [h2]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((2 - Real.sqrt 2) ^ 2 - 4)]
    · -- Case x = 2 + Real.sqrt 2 
      rw [h]
      have h2 : (2 + Real.sqrt 2 : ℝ) + 1 ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      field_simp [h2]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((2 + Real.sqrt 2) ^ 2 - 4)]