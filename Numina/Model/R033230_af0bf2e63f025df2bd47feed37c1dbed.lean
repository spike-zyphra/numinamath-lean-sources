import Mathlib

theorem algebra_26675 : {x : ℝ | x ≥ 2 ∧
    1 / (Real.sqrt x + Real.sqrt (x - 2)) + 1 / (Real.sqrt x + Real.sqrt (x + 2)) = 1 / 4} =
    {257 / 16} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x ≥ 2 ∧ 1 / (Real.sqrt x + Real.sqrt (x - 2)) + 1 / (Real.sqrt x + Real.sqrt (x + 2)) = 1 / 4, prove x = 257 / 16
    rintro ⟨hx1, heq⟩
    have h1 : Real.sqrt x + Real.sqrt (x - 2) ≠ 0 := by
      by_contra h
      have h2 : Real.sqrt x = 0 := by nlinarith [Real.sqrt_nonneg (x), Real.sqrt_nonneg (x - 2)]
      have h3 : x = 0 := by
        rw [Real.sqrt_eq_zero (show 0 ≤ x by linarith)] at h2
        linarith
      linarith
    have h2 : Real.sqrt x + Real.sqrt (x + 2) ≠ 0 := by
      by_contra h
      have h3 : Real.sqrt x = 0 := by nlinarith [Real.sqrt_nonneg (x), Real.sqrt_nonneg (x + 2)]
      have h4 : x = 0 := by
        rw [Real.sqrt_eq_zero (show 0 ≤ x by linarith)] at h3
        linarith
      linarith
    have eq1 : 1 / (Real.sqrt x + Real.sqrt (x - 2)) = (Real.sqrt x - Real.sqrt (x - 2)) / 2 := by
      have h3 : Real.sqrt x + Real.sqrt (x - 2) ≠ 0 := h1
      field_simp [h3]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by nlinarith), Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg x]
    have eq2 : 1 / (Real.sqrt x + Real.sqrt (x + 2)) = (Real.sqrt (x + 2) - Real.sqrt x) / 2 := by
      have h3 : Real.sqrt x + Real.sqrt (x + 2) ≠ 0 := h2
      field_simp [h3]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x + 2 by nlinarith), Real.sqrt_nonneg (x + 2), Real.sqrt_nonneg x]
    rw [eq1, eq2] at heq
    have eq3 : (Real.sqrt x - Real.sqrt (x - 2)) / 2 + (Real.sqrt (x + 2) - Real.sqrt x) / 2 = (Real.sqrt (x + 2) - Real.sqrt (x - 2)) / 2 := by
      ring
    rw [eq3] at heq
    have h3 : Real.sqrt (x + 2) - Real.sqrt (x - 2) = 1 / 2 := by
      linarith
    have h4 : Real.sqrt (x + 2) = Real.sqrt (x - 2) + 1 / 2 := by
      linarith [h3]
    have h5 : Real.sqrt (x + 2) ^ 2 = (Real.sqrt (x - 2) + 1 / 2) ^ 2 := by
      rw [h4]
    have h6 : Real.sqrt (x + 2) ^ 2 = x + 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h7 : Real.sqrt (x - 2) ^ 2 = x - 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h8 : Real.sqrt (x - 2) = 15 / 4 := by
      nlinarith [h5, h6, h7, Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg (x + 2)]
    have h9 : x - 2 = (15 / 4) ^ 2 := by
      calc
        x - 2 = (Real.sqrt (x - 2)) ^ 2 := by rw [Real.sq_sqrt]; all_goals nlinarith
        _ = (15 / 4) ^ 2 := by rw [h8]
    nlinarith
  · -- Assume x = 257 / 16, prove x ≥ 2 ∧ 1 / (Real.sqrt x + Real.sqrt (x - 2)) + 1 / (Real.sqrt x + Real.sqrt (x + 2)) = 1 / 4
    intro hx
    rw [hx]
    constructor
    · norm_num
    · -- Show the equation
      have h1 : Real.sqrt (257 / 16 : ℝ) = (Real.sqrt 257) / 4 := by
        rw [Real.sqrt_div (by norm_num)]
        have h2 : Real.sqrt (16 : ℝ) = 4 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        field_simp [h2]
        all_goals norm_num
      have h2 : Real.sqrt ((257 / 16 : ℝ) - 2) = (15 / 4 : ℝ) := by
        rw [show (257 / 16 : ℝ) - 2 = (225 / 16 : ℝ) by norm_num]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h3 : Real.sqrt ((257 / 16 : ℝ) + 2) = (17 / 4 : ℝ) := by
        rw [show (257 / 16 : ℝ) + 2 = (289 / 16 : ℝ) by norm_num]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h4 : 1 / (Real.sqrt (257 / 16 : ℝ) + Real.sqrt ((257 / 16 : ℝ) - 2)) = ( (Real.sqrt (257 / 16 : ℝ)) - Real.sqrt ((257 / 16 : ℝ) - 2) ) / 2 := by
        rw [h1, h2]
        field_simp
        <;> ring_nf <;> norm_num
        <;> nlinarith [Real.sqrt_nonneg (257 / 16 : ℝ), Real.sqrt_nonneg (257 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (257 : ℝ) by norm_num)]
      have h5 : 1 / (Real.sqrt (257 / 16 : ℝ) + Real.sqrt ((257 / 16 : ℝ) + 2)) = ( (Real.sqrt ((257 / 16 : ℝ) + 2)) - Real.sqrt (257 / 16 : ℝ) ) / 2 := by
        rw [h1, h3]
        field_simp
        <;> ring_nf <;> norm_num
        <;> nlinarith [Real.sqrt_nonneg (257 / 16 : ℝ), Real.sqrt_nonneg (257 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (257 : ℝ) by norm_num)]
      rw [h4, h5]
      rw [h1, h2, h3]
      norm_num
      <;> ring_nf <;> norm_num
      <;> nlinarith [Real.sqrt_nonneg (257 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (257 : ℝ) by norm_num)]