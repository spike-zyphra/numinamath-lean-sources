import Mathlib

theorem algebra_259043 (x : ℝ) (hx : x ≠ 0) :
    16 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) = 16 * x + 1 / x ↔
    x = 1 / 4 ∨ x = -1 / 4 := by
  constructor
  · -- Assume the equation holds, prove the disjunction of the roots
    intro h_eq
    have h1 : 16 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) = 8 * Real.sin (2 * Real.pi * x) := by
      have h2 : Real.sin (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := by
        rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
        rw [Real.sin_two_mul]
      rw [h2]
      ring
    have h_eq2 : 8 * Real.sin (2 * Real.pi * x) = 16 * x + 1 / x := by
      linarith [h_eq, h1]
    have h_eq3 : 8 * Real.sin (2 * Real.pi * x) * x = 16 * x ^ 2 + 1 := by
      have h2 : x ≠ 0 := hx
      have eq1 : 8 * Real.sin (2 * Real.pi * x) = 16 * x + 1 / x := by linarith [h_eq2]
      have eq2 : 8 * Real.sin (2 * Real.pi * x) * x = (16 * x + 1 / x) * x := by
        rw [eq1]
      have eq3 : (16 * x + 1 / x) * x = 16 * x ^ 2 + 1 := by
        field_simp [h2]
        <;> ring
      rw [eq3] at eq2
      linarith [eq2]
    by_cases h3 : x > 0
    · -- Assume x > 0
      have h2 : -1 ≤ Real.sin (2 * Real.pi * x) ∧ Real.sin (2 * Real.pi * x) ≤ 1 := by
        constructor
        · apply Real.neg_one_le_sin
        · apply Real.sin_le_one
      have h4 : -8 * x ≤ 8 * Real.sin (2 * Real.pi * x) * x := by
        nlinarith [h2.1, mul_pos (show 0 < x by linarith) (show 0 < (8 : ℝ) by norm_num), Real.sin_sq_add_cos_sq (2 * Real.pi * x)]
      have h5 : 8 * Real.sin (2 * Real.pi * x) * x ≤ 8 * x := by
        nlinarith [h2.2, mul_pos (show 0 < x by linarith) (show 0 < (8 : ℝ) by norm_num), Real.sin_sq_add_cos_sq (2 * Real.pi * x)]
      have h6 : 16 * x ^ 2 - 8 * x + 1 ≤ 0 := by
        nlinarith [h_eq3, h5]
      have h7 : (x - 1 / 4) ^ 2 ≤ 0 := by
        nlinarith [h6]
      have h8 : x = 1 / 4 := by
        nlinarith [h7]
      left
      exact h8
    · -- Assume x ≤ 0
      push_neg at h3
      have h4 : x < 0 := by
        by_contra h
        push_neg at h
        have : x = 0 := by linarith
        contradiction
      have h2 : -1 ≤ Real.sin (2 * Real.pi * x) ∧ Real.sin (2 * Real.pi * x) ≤ 1 := by
        constructor
        · apply Real.neg_one_le_sin
        · apply Real.sin_le_one
      have h4 : -8 * x ≥ 8 * Real.sin (2 * Real.pi * x) * x := by
        nlinarith [h2.1, mul_pos (show 0 < -x by linarith) (show 0 < (8 : ℝ) by norm_num), Real.sin_sq_add_cos_sq (2 * Real.pi * x)]
      have h5 : 8 * Real.sin (2 * Real.pi * x) * x ≥ 8 * x := by
        nlinarith [h2.2, mul_pos (show 0 < -x by linarith) (show 0 < (8 : ℝ) by norm_num), Real.sin_sq_add_cos_sq (2 * Real.pi * x)]
      have h8 : 16 * x ^ 2 + 8 * x + 1 ≤ 0 := by
        nlinarith [h_eq3, h4]
      have h9 : (x + 1 / 4) ^ 2 ≤ 0 := by
        nlinarith [h8]
      have h10 : x = -1 / 4 := by
        nlinarith [h9]
      right
      exact h10
  · -- Assume the roots, prove the equation
    rintro (h_eq | h_eq)
    · -- Case x = 1/4
      rw [h_eq]
      have h1 : Real.sin (Real.pi * (1/4 : ℝ)) = Real.sqrt 2 / 2 := by
        have : Real.pi * (1/4 : ℝ) = Real.pi / 4 := by ring
        rw [this]
        rw [Real.sin_pi_div_four]
      have h2 : Real.cos (Real.pi * (1/4 : ℝ)) = Real.sqrt 2 / 2 := by
        have : Real.pi * (1/4 : ℝ) = Real.pi / 4 := by ring
        rw [this]
        rw [Real.cos_pi_div_four]
      rw [h1, h2]
      field_simp
      <;> ring_nf <;> norm_num
    · -- Case x = -1/4
      rw [h_eq]
      have h1 : Real.sin (Real.pi * (-1/4 : ℝ)) = -Real.sqrt 2 / 2 := by
        have : Real.pi * (-1/4 : ℝ) = - (Real.pi / 4) := by ring
        rw [this]
        rw [Real.sin_neg]
        rw [Real.sin_pi_div_four]
        all_goals ring
      have h2 : Real.cos (Real.pi * (-1/4 : ℝ)) = Real.sqrt 2 / 2 := by
        have : Real.pi * (-1/4 : ℝ) = - (Real.pi / 4) := by ring
        rw [this]
        rw [Real.cos_neg]
        rw [Real.cos_pi_div_four]
      rw [h1, h2]
      field_simp
      <;> ring_nf <;> norm_num