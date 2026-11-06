import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21404 :
  IsLeast {y : ℝ | ∃ x > 1, y = 17 * logb 30 x - 3 * logb x 5 + 20 * logb x 15 - 3 * logb x 6 + 20 * logb x 2} 34 := by
  constructor
  · -- Show 34 is in the set
    use 30
    constructor
    · norm_num
    · -- Show that when x = 30, the expression is 34
      have h1 : 17 * logb 30 30 - 3 * logb 30 5 + 20 * logb 30 15 - 3 * logb 30 6 + 20 * logb 30 2 = 34 := by
        have h2 : logb 30 30 = 1 := by
          rw [logb_eq_iff_rpow_eq] <;> (norm_num)
        have h3 : logb 30 5 = (log 5) / (log 30) := by
          field_simp [logb]
        have h4 : logb 30 15 = (log 15) / (log 30) := by
          field_simp [logb]
        have h5 : logb 30 6 = (log 6) / (log 30) := by
          field_simp [logb]
        have h6 : logb 30 2 = (log 2) / (log 30) := by
          field_simp [logb]
        rw [h2, h3, h4, h5, h6]
        have h7 : log 15 = log 3 + log 5 := by
          calc
            log 15 = log (3 * 5) := by norm_num
            _ = log 3 + log 5 := by rw [log_mul (by norm_num) (by norm_num)]
        have h8 : log 6 = log 2 + log 3 := by
          calc
            log 6 = log (2 * 3) := by norm_num
            _ = log 2 + log 3 := by rw [log_mul (by norm_num) (by norm_num)]
        have h9 : log 30 = log 2 + log 3 + log 5 := by
          calc
            log 30 = log (2 * 3 * 5) := by norm_num
            _ = log (2 * 3) + log 5 := by rw [log_mul (by norm_num) (by norm_num)]
            _ = log 2 + log 3 + log 5 := by
              rw [log_mul (by norm_num) (by norm_num)]
              all_goals ring
        rw [h7, h8, h9]
        field_simp
        nlinarith
      linarith [h1]
  · -- Show there is no smaller element in the set
    intro y hy
    rcases hy with ⟨x, hx, heq⟩
    have h1 : 17 * logb 30 x - 3 * logb x 5 + 20 * logb x 15 - 3 * logb x 6 + 20 * logb x 2 = 17 * ( (log x) / (log 30) + (log 30) / (log x) ) := by
      have h2 : logb 30 x = (log x) / (log (30 : ℝ)) := by
        field_simp [logb]
      have h3 : logb x 5 = (log 5) / (log x) := by
        field_simp [logb]
      have h4 : logb x 15 = (log 15) / (log x) := by
        field_simp [logb]
      have h5 : logb x 6 = (log 6) / (log x) := by
        field_simp [logb]
      have h6 : logb x 2 = (log 2) / (log x) := by
        field_simp [logb]
      have h7 : log 15 = log 3 + log 5 := by
        calc
          log 15 = log (3 * 5) := by norm_num
          _ = log 3 + log 5 := by rw [log_mul (by norm_num) (by norm_num)]
      have h8 : log 6 = log 2 + log 3 := by
        calc
          log 6 = log (2 * 3) := by norm_num
          _ = log 2 + log 3 := by rw [log_mul (by norm_num) (by norm_num)]
      have h9 : log 30 = log 2 + log 3 + log 5 := by
        calc
          log 30 = log (2 * 3 * 5) := by norm_num
          _ = log (2 * 3) + log 5 := by rw [log_mul (by norm_num) (by norm_num)]
          _ = log 2 + log 3 + log 5 := by
            rw [log_mul (by norm_num) (by norm_num)]
            all_goals ring
      rw [h2, h3, h4, h5, h6]
      rw [h7, h8, h9]
      field_simp
      <;> ring
    have h2 : (log x) > 0 := by
      apply log_pos
      linarith
    have h3 : log 30 > 0 := by
      apply log_pos
      norm_num
    have h5 : (log x) / (log 30) + (log 30) / (log x) ≥ 2 := by
      have h_pos1 : (log x) > 0 := h2
      have h_pos2 : (log 30) > 0 := h3
      have h_pos3 : (log x) * (log 30) > 0 := mul_pos h2 h3
      have h5 : (log x) / (log 30) + (log 30) / (log x) - 2 ≥ 0 := by
        have h6 : (log x) / (log 30) + (log 30) / (log x) - 2 = ((log x) ^ 2 + (log 30) ^ 2 - 2 * (log x) * (log 30)) / ((log x) * (log 30)) := by
          field_simp
          ring
        rw [h6]
        have h7 : ((log x) ^ 2 + (log 30) ^ 2 - 2 * (log x) * (log 30)) ≥ 0 := by
          have h8 : ((log x) - (log 30)) ^ 2 ≥ 0 := sq_nonneg ((log x) - (log 30))
          linarith [h8]
        have h8 : (log x) * (log 30) > 0 := h_pos3
        apply div_nonneg
        linarith
        nlinarith
      linarith
    have h6 : 17 * ( (log x) / (log 30) + (log 30) / (log x) ) ≥ 34 := by
      nlinarith [h5]
    have h7 : y = 17 * ( (log x) / (log 30) + (log 30) / (log x) ) := by
      linarith [heq, h1]
    nlinarith [h7, h6]