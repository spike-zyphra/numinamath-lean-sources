import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_133581 {f : ℝ → ℝ} (hf : f = λ x => logb (1/5) (abs (x - 2))) :
    MonotoneOn (-f) {x | 2 < x} := by
  intro x hx y hy hxy
  have h1 : 2 < x := hx
  have h2 : 2 < y := hy
  have h3 : abs (x - 2) = x - 2 := by
    rw [abs_of_pos]
    nlinarith
  have h4 : abs (y - 2) = y - 2 := by
    rw [abs_of_pos]
    nlinarith
  simp [hf, h3, h4]
  have h5 : logb (1 / 5) (y - 2) ≤ logb (1 / 5) (x - 2) := by
    have h6 : logb (1 / 5) (y - 2) ≤ logb (1 / 5) (x - 2) := by
      have h7 : logb (1 / 5) (y - 2) = (log (y - 2) ) / (log (1 / 5) ) := by 
        field_simp [logb]
      have h8 : logb (1 / 5) (x - 2) = (log (x - 2) ) / (log (1 / 5) ) := by 
        field_simp [logb]
      rw [h7, h8]
      have h10 : log (1 / 5 : ℝ) < 0 := by
        have h11 : log (1 / 5 : ℝ) < log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals norm_num 
        have h12 : log (1 : ℝ) = 0 := Real.log_one 
        linarith [h11, h12] 
      have h13 : log (x - 2) ≤ log (y - 2) := by 
        apply Real.log_le_log 
        all_goals linarith 
      have h14 : (log (y - 2) ) / (log (1 / 5) ) ≤ (log (x - 2) ) / (log (1 / 5) ) := by
        apply (div_le_div_right_of_neg h10).mpr 
        linarith 
      linarith 
    linarith
  linarith
  all_goals nlinarith
  <;> try norm_num
  <;> try linarith
  <;> try norm_num
  <;> try linarith
  <;> try norm_num
  <;> try linarith