import Mathlib

theorem algebra_301690 (x : ℝ) : (12 * x + 5) ^ 2 * (6 * x - 1) * (x + 1) = 55 / 2 ↔
    x = (-5 + 2 * Real.sqrt 15) / 12 ∨ x = (-5 - 2 * Real.sqrt 15) / 12 := by 
  constructor
  · -- Forward: If the equation holds, then the solutions are as given.
    intro h
    have h1 : (12 * x + 5) ^ 2 * (6 * x - 1) * (x + 1) = 55 / 2 := h
    -- The equation is polynomial of 4 degree, which is reduced to quadratic using substitution y^2 = 12x+5
    -- Computing ... we perform substitution automatically manually following
    have h6 : (12 * x + 5 : ℝ) ^ 4 - 49 * (12 * x + 5 : ℝ) ^ 2 - 660 = 0 := by
      nlinarith [sq_nonneg (x + 5 / 12), sq_nonneg (12 * x + 5), sq_nonneg ((12 * x + 5) ^ 2 - 49)]
    -- Now, replacing $y = (12x+5)$, we get the quadratic equation.
    have h7 : ((12 * x + 5) ^ 2 - 60) * ((12 * x + 5) ^ 2 + 11) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- First equation: ((12 * x + 5) ^ 2 - 60) = 0
      have h10 : (12 * x + 5) ^ 2 = 60 := by
        linarith
      have h11 : 12 * x + 5 = Real.sqrt 60 ∨ 12 * x + 5 = -Real.sqrt 60 := by
        have h22 : (12 * x + 5: ℝ) ^ 2 = 60 := h10
        have : (12 * x + 5: ℝ) = Real.sqrt 60 ∨ (12 * x + 5: ℝ) = -Real.sqrt 60 := by
          apply eq_or_eq_neg_of_sq_eq_sq
          norm_num
          nlinarith [Real.sqrt_nonneg 60, Real.sq_sqrt (show (0 : ℝ) ≤ (60 : ℝ) by norm_num)]
        tauto
      cases h11 with
      | inl h12 =>
        -- Solving $12x+5$ to get value.
        -- $\sqrt{60}=2\sqrt{15}$ 
        have h13 : x = (-5 + 2 * Real.sqrt 15) / 12 := by
          nlinarith [Real.sqrt_nonneg 60, Real.sq_sqrt (show (0 : ℝ) ≤ (60 : ℝ) by norm_num), h12,
            Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num),
            show Real.sqrt (60 : ℝ) = 2 * Real.sqrt (15 : ℝ) by
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
              <;> ring_nf <;> norm_num
          ]
        left
        linarith
      | inr h14 =>
        have h15 : x = (-5 - 2 * Real.sqrt 15) / 12 := by
          nlinarith [Real.sqrt_nonneg 60, Real.sq_sqrt (show (0 : ℝ) ≤ (60 : ℝ) by norm_num), h14,
            Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num),
            show Real.sqrt (60 : ℝ) = 2 * Real.sqrt (15 : ℝ) by
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
              <;> ring_nf <;> norm_num
          ]
        right
        linarith
    · -- Second equation: ((12 * x + 5) ^ 2 + 11) = 0
      have h12 : (12 * x + 5) ^ 2 + 11 = 0 := by
        linarith
      nlinarith [sq_nonneg (12 * x + 5)]
  · -- Backward: If the solutions are given, then the equation holds.
    rintro (h | h)
    · -- First solution
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 15 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num), Real.sqrt_nonneg 15]
    · -- Second solution
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 15 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num), Real.sqrt_nonneg 15]