import Mathlib

theorem algebra_204387 :
    {x : ℝ | 0 ≤ 2 * x + 7 ∧ |x| ≥ Real.sqrt 7 ∧ Real.sqrt (2 * x + 7) = (x ^ 2 - 7) / 2} = 
    { -3, 1 + 2 * Real.sqrt 2 } := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x in left side set, prove in right side set (⊆)
    intro h 
    rcases h with ⟨h1, h2, h3⟩
    have h4 : Real.sqrt (2 * x + 7) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h5 : (x ^ 2 - 7) / 2 ≥ 0 := by
      by_contra h
      push_neg at h 
      have h6 : Real.sqrt (2 * x + 7) < 0 := by
        nlinarith [h3, h]
      linarith [Real.sqrt_nonneg (2 * x + 7), h6]
    have h8 : Real.sqrt (2 * x + 7) = (x ^ 2 - 7) / 2 := h3 
    have h9 : (Real.sqrt (2 * x + 7)) ^ 2 = ((x ^ 2 - 7) / 2) ^ 2 := by 
      rw [h8]
    have h10 : (Real.sqrt (2 * x + 7)) ^ 2 = 2 * x + 7 := by
      rw [Real.sq_sqrt]
      linarith 
    rw [h10] at h9
    have h11 : (x + 3) * (x - 1) * (x ^ 2 - 2 * x - 7) = 0 := by
      nlinarith [sq_nonneg (x + 3), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 2 * x - 7), Real.sqrt_nonneg (2 * x + 7)]
    cases' (mul_eq_zero.mp h11) with h12 h13
    cases' (mul_eq_zero.mp h12) with h14 h15
    · -- h14 : x + 3 = 0 
      left 
      linarith 
    · -- h15 : x - 1 = 0 
      exfalso 
      have h16 : x = 1 := by linarith 
      rw [h16] at h3 
      nlinarith [Real.sqrt_nonneg (2 * (1 : ℝ) + 7), Real.sq_sqrt (show (2 * (1 : ℝ) + 7) ≥ 0 by norm_num)]
    · -- h13 : x ^ 2 - 2 * x - 7 = 0
      have h18 : x ^ 2 - 2 * x - 7 = 0 := by linarith 
      have h19 : x = 1 + 2 * Real.sqrt 2 ∨ x = 1 - 2 * Real.sqrt 2 := by 
        have h17 : x ^ 2 - 2 * x - 7 = 0 := h18 
        have h20 : x ^ 2 - 2 * x - 7 = (x - (1 + 2 * Real.sqrt 2)) * (x - (1 - 2 * Real.sqrt 2)) := by 
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
        rw [h20] at h17 
        cases' (mul_eq_zero.mp h17) with h21 h22
        · -- h21 : x - (1 + 2 * Real.sqrt 2) = 0 
          left 
          linarith 
        · -- h22 : x - (1 - 2 * Real.sqrt 2) = 0 
          right 
          linarith 
      cases' h19 with h20 h21 
      · -- x = 1 + 2 * Real.sqrt 2 
        right 
        linarith 
      · -- x = 1 - 2 * Real.sqrt 2 
        exfalso 
        have h22 : x = (1 - 2 * Real.sqrt 2) := by linarith 
        rw [h22] at h3 
        nlinarith [Real.sqrt_nonneg (2 * (1 - 2 * Real.sqrt 2) + 7), Real.sq_sqrt (show (2 * (1 - 2 * Real.sqrt 2) + 7 : ℝ) ≥ 0 by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num) ]), Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  · -- Show the reverse (⊇)
    intro h 
    rcases h with (rfl | rfl)
    · -- x = -3 
      constructor
      · -- Show 0 ≤ 2 * x + 7 
        norm_num 
      constructor
      · -- Show |x| ≥ Real.sqrt 7 
        have h1 : |(-3 : ℝ)| = 3 := by 
          norm_num [abs_of_nonneg]
        rw [h1] 
        have h2 : Real.sqrt 7 ≤ 3 := by 
          rw [Real.sqrt_le_left]
          all_goals norm_num 
        linarith 
      · -- Show Real.sqrt (2 * x + 7) = (x ^ 2 - 7) / 2 
        have h3 : Real.sqrt (2 * (-3 : ℝ) + 7) = 1 := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h3] 
        all_goals norm_num 
    · -- x = 1 + 2 * Real.sqrt 2 
      constructor 
      · -- Show 0 ≤ 2 * x + 7 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      constructor 
      · -- Show |x| ≥ Real.sqrt 7 
        have h3 : |(1 + 2 * Real.sqrt 2 : ℝ)| = 1 + 2 * Real.sqrt 2 := by
          apply abs_of_pos 
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        rw [h3] 
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · -- Show Real.sqrt (2 * x + 7) = (x ^ 2 - 7) / 2 
        have h4 : Real.sqrt (2 * (1 + 2 * Real.sqrt 2 : ℝ) + 7) = 1 + 2 * Real.sqrt 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        rw [h4] 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]