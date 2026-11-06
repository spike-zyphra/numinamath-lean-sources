import Mathlib

open Real Set

theorem algebra_4608 :
  IsLeast {t : ℝ | ∃ x y : ℝ, x ∈ Ioo (-2) 2 ∧ y ∈ Ioo (-2) 2 ∧ x * y = -1 ∧ t = 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2)} (12 / 5) := by
  constructor
  · -- Show that 12/5 is in the set.
    use Real.sqrt (2 / 3), -Real.sqrt (3 / 2)
    constructor 
    · -- Show x ∈ (-2, 2)
      constructor 
      · -- Show -2 < Real.sqrt (2 / 3)
        have h1 : -2 < Real.sqrt (2 / 3) := by 
          have h2 : Real.sqrt (2 / 3) > 0 := by positivity 
          linarith 
        exact h1 
      · -- Show Real.sqrt (2 / 3) < 2
        have h1 : Real.sqrt (2 / 3) < 2 := by 
          rw [Real.sqrt_lt] <;> norm_num 
        exact h1 
    constructor 
    · -- Show y ∈ (-2, 2)
      constructor 
      · -- Show -2 < -Real.sqrt (3 / 2)
        have h1 : -Real.sqrt (3 / 2) > -2 := by 
          have h2 : Real.sqrt (3 / 2) < 2 := by 
            rw [Real.sqrt_lt] <;> norm_num 
          linarith 
        exact h1 
      · -- Show -Real.sqrt (3 / 2) < 2 
        have h1 : -Real.sqrt (3 / 2) < 2 := by 
          have h2 : Real.sqrt (3 / 2) > 0 := by positivity 
          linarith 
        exact h1 
    constructor 
    · -- Show x * y = -1
      have h5 : Real.sqrt (2 / 3) * Real.sqrt (3 / 2) = 1 := by
        have h1 : Real.sqrt (2 / 3) * Real.sqrt (3 / 2) = Real.sqrt ((2 / 3 : ℝ) * (3 / 2 : ℝ)) := by 
          rw [← Real.sqrt_mul (by norm_num)]
        have h2 : (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 := by norm_num 
        rw [h2] at h1 
        have h3 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one 
        rw [h3] at h1 
        linarith 
      have h5' : Real.sqrt (2 / 3) * (-Real.sqrt (3 / 2)) = -1 := by 
        have h6 : Real.sqrt (2 / 3) * Real.sqrt (3 / 2) = 1 := h5 
        nlinarith 
      linarith [h5']
    · -- Show 12 / 5 = 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2)
      have h1 : Real.sqrt (2 / 3) ^ 2 = (2 / 3 : ℝ) := Real.sq_sqrt (by norm_num) 
      have h2 : (-Real.sqrt (3 / 2) : ℝ) ^ 2 = (3 / 2 : ℝ) := by 
        have h3 : Real.sqrt (3 / 2) ^ 2 = (3 / 2 : ℝ) := Real.sq_sqrt (by norm_num) 
        linarith 
      field_simp [h1, h2]
      nlinarith [Real.sqrt_nonneg (2 / 3 : ℝ), Real.sqrt_nonneg (3 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 / 3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 / 2 : ℝ) by norm_num)]
  · -- Show that 12/5 is the minimum. 
    intro t ht 
    rcases ht with ⟨x, y, hx, hy, hxy, ht⟩ 
    rcases hx with ⟨hx1, hx2⟩ 
    rcases hy with ⟨hy1, hy2⟩ 
    have h14 : 4 - x^2 > 0 := by 
      nlinarith 
    have h15 : 9 - y^2 > 0 := by 
      nlinarith 
    have h35 : 4 * (9 - y^2) * 5 + 9 * (4 - x^2) * 5 - 12 * (4 - x^2) * (9 - y^2) ≥ 0 := by 
      nlinarith [sq_nonneg (x ^ 2 - 2 / 3), sq_nonneg (y ^ 2 - 3 / 2), sq_nonneg (x * y + 1), 
          sq_nonneg (x^2 - 2/3), sq_nonneg (y^2 - 3/2), 
          sq_nonneg (x - y), sq_nonneg (x + y), 
          mul_pos (show (0 : ℝ) < 4 - x^2 by nlinarith) (show (0 : ℝ) < 9 - y^2 by nlinarith), 
          hxy
        ]
    have h36 : (4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5) ≥ 0 := by 
      have h4 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5 =
          (4 * (9 - y ^ 2) * 5 + 9 * (4 - x ^ 2) * 5 - 12 * (4 - x ^ 2) * (9 - y ^ 2)) / ((4 - x ^ 2) * (9 - y ^ 2) * 5) := by 
        field_simp 
        ring 
      rw [h4] at *
      apply div_nonneg 
      linarith [h35]
      have h38 : (4 - x ^ 2) * (9 - y ^ 2) * (5 : ℝ) > 0 := by 
        have h39 : 0 < (4 - x^2 : ℝ) := by nlinarith 
        have h40 : 0 < (9 - y^2 : ℝ) := by nlinarith 
        positivity 
      linarith
    linarith [ht, h36]