import Mathlib

theorem algebra_287819 :
  {(x, y) : ℝ × ℝ | 
    x + 5 ≥ 0 ∧ 
    y + 2 ≥ 0 ∧
    4 / Real.sqrt (x + 5) - 3 / Real.sqrt (y + 2) = 1 ∧ 
    2 / Real.sqrt (x + 5) + 9 / Real.sqrt (y + 2) = 4} =
  {(-1, 7)} := by
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- First direction
    rintro ⟨hx1, hy1, heq1, heq2⟩
    by_cases h1 : x + 5 > 0
    · -- Case x + 5 > 0
      by_cases h2 : y + 2 > 0
      · -- Case y + 2 > 0
        have h11 : 0 < Real.sqrt (x + 5) := by
          apply Real.sqrt_pos.2
          linarith
        have h12 : 0 < Real.sqrt (y + 2) := by
          apply Real.sqrt_pos.2
          linarith
        have eq1 : 4 * (Real.sqrt (y + 2)) - 3 * (Real.sqrt (x + 5)) = Real.sqrt (x + 5) * Real.sqrt (y + 2) := by
          have h13 : Real.sqrt (y + 2) > 0 := h12
          have h14 : Real.sqrt (x + 5) > 0 := h11
          field_simp at heq1
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x + 5 by linarith), 
            Real.sq_sqrt (show (0 : ℝ) ≤ y + 2 by linarith), 
            mul_pos h11 h12
          ]
        have eq2 : 2 * (Real.sqrt (y + 2)) + 9 * (Real.sqrt (x + 5)) = 4 * (Real.sqrt (x + 5) * Real.sqrt (y + 2)) := by
          have h13 : Real.sqrt (y + 2) > 0 := h12
          have h14 : Real.sqrt (x + 5) > 0 := h11
          field_simp at heq2
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x + 5 by linarith), 
            Real.sq_sqrt (show (0 : ℝ) ≤ y + 2 by linarith), 
            mul_pos h11 h12
          ]
        have eq3 : (Real.sqrt (x + 5) )^2 = (x + 5) := by 
          rw [Real.sq_sqrt]
          nlinarith
        have eq4 : (Real.sqrt (y + 2)) ^ 2 = (y + 2) := by 
          rw [Real.sq_sqrt]
          nlinarith
        have eq5 : (Real.sqrt (x + 5) ) = (2 : ℝ) := by 
          nlinarith [sq_nonneg (Real.sqrt (x + 5) - 2), sq_nonneg (Real.sqrt (y + 2) - 3), 
            Real.sq_sqrt (show (0 : ℝ) ≤ x + 5 by linarith), 
            Real.sq_sqrt (show (0 : ℝ) ≤ y + 2 by linarith), 
            mul_pos h11 h12
          ]
        have eq6 : (Real.sqrt (y + 2)) = (3 : ℝ) := by 
          nlinarith [sq_nonneg (Real.sqrt (x + 5) - 2), sq_nonneg (Real.sqrt (y + 2) - 3), 
            Real.sq_sqrt (show (0 : ℝ) ≤ x + 5 by linarith), 
            Real.sq_sqrt (show (0 : ℝ) ≤ y + 2 by linarith), 
            mul_pos h11 h12
          ]
        have eq7 : x = -1 := by
          have h71 : (Real.sqrt (x + 5)) ^ 2 = 4 := by
            rw [eq5]
            norm_num
          have h72 : (x + 5) = 4 := by
            have h71' : (Real.sqrt (x + 5)) ^ 2 = (x + 5) := by
              rw [Real.sq_sqrt]
              all_goals nlinarith
            nlinarith
          linarith
        have eq8 : y = 7 := by 
          have h81 : (Real.sqrt (y + 2)) ^ 2 = 9 := by
            rw [eq6]
            norm_num
          have h82 : (y + 2) = 9 := by 
            have h81' : (Real.sqrt (y + 2)) ^ 2 = (y + 2) := by
              rw [Real.sq_sqrt]
              all_goals nlinarith
            nlinarith
          linarith
        simp [eq7, eq8]
      · -- Case y + 2 ≤ 0, contradicts hy1 
        have hy2 : y + 2 = 0 := by 
          nlinarith
        have y1 : Real.sqrt (y + 2) = (0 : ℝ) := by
          rw [show y + 2 = (0 : ℝ) by linarith]
          simp
        rw [y1] at heq1 heq2 
        have eq3 : 4 / Real.sqrt (x + 5) = 1 := by
          field_simp at heq1 ⊢
          linarith
        have eq4 : 2 / Real.sqrt (x + 5) = 4 := by
          field_simp at heq2 ⊢
          linarith
        have hx3 : Real.sqrt (x + 5) = 4 := by
          field_simp at eq3 ⊢
          nlinarith
        have hx4 : Real.sqrt (x + 5) = 1 / 2 := by
          field_simp at eq4 ⊢
          nlinarith
        have h3 : Real.sqrt (x + 5) ≥ 0 := by 
          apply Real.sqrt_nonneg 
        nlinarith [hx3, hx4, h3]
    · -- Case x + 5 ≤ 0, contradicts hx1 
      by_cases h2 : y + 2 > 0 
      · -- Case y + 2 > 0, but x+5 =0 
        have h13 : Real.sqrt (x + 5) = 0 := by 
          rw [Real.sqrt_eq_zero']
          all_goals nlinarith 
        rw [h13] at heq1 heq2 
        have h14 : Real.sqrt (y + 2) > 0 := by
          apply Real.sqrt_pos.2
          linarith 
        field_simp at heq1 heq2 
        all_goals nlinarith [Real.sqrt_nonneg (y + 2)]
      · -- Case y + 2 ≤ 0
        have h15 : Real.sqrt (x + 5) = 0 := by 
          rw [Real.sqrt_eq_zero']
          all_goals nlinarith 
        have h16 : Real.sqrt (y + 2) = 0 := by 
          rw [Real.sqrt_eq_zero']
          all_goals nlinarith 
        rw [h15, h16] at heq1 heq2 
        all_goals nlinarith 
  · -- Second direction
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show first equation
      have h1 : Real.sqrt (4 : ℝ) = 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (9 : ℝ) = 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : Real.sqrt (-1 + 5) = 2 := by
        rw [show -1 + 5 = (4 : ℝ) by nlinarith]
        rw [h1]
      have h4 : Real.sqrt ((7 + 2 : ℝ)) = 3 := by
        rw [show (7 + 2 : ℝ) = (9 : ℝ) by nlinarith]
        rw [h2]
      rw [h3, h4]
      all_goals norm_num
    · -- Show second equation
      have h1 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (9 : ℝ) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : Real.sqrt (-1 + 5) = 2 := by
        rw [show -1 + 5 = (4 : ℝ) by nlinarith]
        rw [h1]
      have h4 : Real.sqrt ((7 + 2 : ℝ)) = 3 := by
        rw [show (7 + 2 : ℝ) = (9 : ℝ) by nlinarith]
        rw [h2]
      rw [h3, h4]
      all_goals norm_num