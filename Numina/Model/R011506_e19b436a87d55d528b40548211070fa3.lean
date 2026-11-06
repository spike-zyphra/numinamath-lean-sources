import Mathlib

theorem algebra_159224 :
    {x : ℝ | x ≥ 8 ∧ Real.sqrt (x - 8) ≠ 4 ∧ Real.sqrt (x - 8) ≠ 9 ∧ 6 / (Real.sqrt (x - 8) - 9) + 1 / (Real.sqrt (x - 8) - 4) + 7 / (Real.sqrt (x - 8) + 4) + 12 / (Real.sqrt (x - 8) + 9) = 0} = {17, 44} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x in the left side, prove x in the right side.
    rintro ⟨hx1, hx2, hx3, heq⟩
    have h2 : x - 8 ≥ 0 := by linarith
    have h3 : Real.sqrt (x - 8) ≥ 0 := Real.sqrt_nonneg (x - 8)
    have h4 : Real.sqrt (x - 8) ^ 2 = x - 8 := Real.sq_sqrt (by linarith)
    -- Manipulate eq to clear denominators
    have h5 : Real.sqrt (x - 8) - 9 ≠ 0 := by
      intro h
      apply hx3
      linarith
    have h6 : Real.sqrt (x - 8) - 4 ≠ 0 := by
      intro h
      apply hx2
      linarith
    have h7 : Real.sqrt (x - 8) + 4 ≠ 0 := by 
      nlinarith [Real.sqrt_nonneg (x - 8)]
    have h8 : Real.sqrt (x - 8) + 9 ≠ 0 := by 
      nlinarith [Real.sqrt_nonneg (x - 8)]
    field_simp [h5, h6, h7, h8] at heq 
    have h1 : (Real.sqrt (x - 8) - 3) * (Real.sqrt (x - 8) - 6) = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (x - 8) ^ 2 - 36), sq_nonneg (Real.sqrt (x - 8) ^ 2 - 9), sq_nonneg (Real.sqrt (x - 8) - 3), sq_nonneg (Real.sqrt (x - 8) - 6), Real.sqrt_nonneg (x - 8), sq_nonneg (Real.sqrt (x - 8) ^ 2), h4]
    cases' (mul_eq_zero.mp h1) with h9 h10
    · -- Real.sqrt (x - 8) - 3 = 0
      have h11 : Real.sqrt (x - 8) = 3 := by nlinarith 
      have h12 : x - 8 = 9 := by 
        calc 
          x - 8 = (Real.sqrt (x - 8)) ^ 2 := by rw [Real.sq_sqrt]; nlinarith 
          _ = 3 ^ 2 := by rw [h11]
          _ = 9 := by norm_num 
      have h13 : x = 17 := by linarith 
      left 
      linarith
    · -- Real.sqrt (x - 8) - 6 = 0
      have h12 : Real.sqrt (x - 8) = 6 := by nlinarith 
      have h13 : x - 8 = 36 := by 
        calc 
          x - 8 = (Real.sqrt (x - 8)) ^ 2 := by rw [Real.sq_sqrt]; nlinarith 
          _ = 6 ^ 2 := by rw [h12]
          _ = 36 := by norm_num 
      have h14 : x = 44 := by linarith 
      right 
      linarith 
  · -- Show that {17, 44} is contained in the left side.
    rintro (rfl | rfl)
    · -- x = 17
      constructor 
      · norm_num 
      constructor 
      · -- Show sqrt 17 - 8 ≠ 4 
        rw [show Real.sqrt ((17 : ℝ) - 8) = (3 : ℝ) by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        ]
        norm_num 
      constructor 
      · -- Show sqrt 17 - 8 ≠ 9 
        rw [show Real.sqrt ((17 : ℝ) - 8) = (3 : ℝ) by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        ]
        norm_num 
      · -- Show the equation holds 
        have h13 : Real.sqrt ((17 : ℝ) - 8) = (3 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h13] 
        norm_num 
    · -- x = 44 
      constructor 
      · -- Show x ≥ 8 
        norm_num 
      constructor 
      · -- Show sqrt 44 - 8 ≠ 4 
        rw [show Real.sqrt ((44 : ℝ) - 8) = (6 : ℝ) by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        ]
        norm_num 
      constructor 
      · -- Show sqrt 44 - 8 ≠ 9 
        rw [show Real.sqrt ((44 : ℝ) - 8) = (6 : ℝ) by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        ]
        norm_num 
      · -- Show the equation holds 
        have h14 : Real.sqrt ((44 : ℝ) - 8) = (6 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h14] 
        norm_num