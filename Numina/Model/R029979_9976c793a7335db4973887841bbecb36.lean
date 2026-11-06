import Mathlib

open Real

theorem algebra_317458 {n m : ℝ} (hn : 1 < n) (hm : n < m) :
    logb n m > logb m n ∧ logb m n > logb (1 / n) m := by
  have h1 : 1 < m := by linarith
  have h6 : log n > 0 := by
    apply log_pos
    linarith
  have h7 : log m > 0 := by
    apply log_pos
    linarith
  have h9 : log m > log n := by
    apply Real.log_lt_log
    all_goals linarith
  have h10 : 0 < (log n : ℝ) := h6
  have h11 : 0 < (log m : ℝ) := h7
  have h12 : 0 < (log m : ℝ) * (log n : ℝ) := mul_pos h7 h6
  have h2 : logb n m > logb m n := by
    have h3 : logb n m = (log m) / (log n) := by
      field_simp [logb]
    have h4 : logb m n = (log n) / (log m) := by
      field_simp [logb]
    rw [h3, h4]
    have h13 : (log m) / (log n) > (log n) / (log m) := by
      have h14 : (log m) / (log n) - (log n) / (log m) > 0 := by
        have h15 : (log m) / (log n) - (log n) / (log m) = ( (log m)^2 - (log n)^2 ) / ( (log n) * (log m) ) := by
          field_simp
          <;> ring
        rw [h15]
        have h16 : (log m) ^ 2 > (log n) ^ 2 := by nlinarith [h6, h7, h9, h10]
        have h17 : (log m) ^ 2 - (log n) ^ 2 > 0 := by linarith
        have h18 : (log n) * (log m) > 0 := by positivity
        apply div_pos
        all_goals linarith
      linarith
    linarith
  have h5 : logb m n > logb (1 / n) m := by
    have h11 : logb m n = (log n) / (log m) := by
      field_simp [logb]
      all_goals tauto
    have h12 : logb (1 / n) m = - (log m / (log n)) := by
      have h13 : logb (1 / n) m = (log m) / (log (1 / n)) := by
        field_simp [logb]
        all_goals tauto
      have h14 : log (1 / n) = - (log n) := by
        simp [log_div, log_one]
      rw [h13, h14]
      <;> ring_nf <;> field_simp <;> ring
    rw [h11]
    have h13 : (log n) / (log m) > - (log m / (log n)) := by
      have h8 : (log n) / (log m) - ( - (log m / (log n)) ) > 0 := by
        have h9 : (log n) / (log m) - ( - (log m / (log n)) ) = ( (log n) ^ 2 + (log m) ^ 2 ) / ( (log n) * (log m) ) := by
          field_simp
          <;> ring
        rw [h9]
        have h10 : (log n) > 0 := by
          apply log_pos
          linarith
        have h11 : (log m) > 0 := by
          apply log_pos
          linarith
        have h12 : (log n) ^ 2 + (log m) ^ 2 > 0 := by
          have h13 : (log n) ^ 2 > 0 := by
            nlinarith [show (log n) > 0 by apply log_pos; linarith]
          have h14 : (log m) ^ 2 > 0 := by
            nlinarith [show (log m) > 0 by apply log_pos; linarith]
          linarith
        have h13 : (log n) * (log m) > 0 := by
          positivity
        apply div_pos
        all_goals linarith
      linarith
    have h14 : (log n) / (log m) > - (log m / (log n)) := h13
    rw [h12]
    all_goals
      linarith
  exact ⟨h2, h5⟩