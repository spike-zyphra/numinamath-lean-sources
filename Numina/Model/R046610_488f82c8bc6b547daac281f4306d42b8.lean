import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9096 {f : ℝ → ℝ} (hf : f = λ x => Real.log x / x) :
    AntitoneOn f (Set.Ioi (Real.exp 1)) := by
  intro x hx y hy hxy
  have h1 : Real.exp 1 < x := by
    simpa using hx
  have h2 : Real.exp 1 < y := by
    simpa using hy
  have h3 : x ≤ y := hxy
  have h4 : Real.log x > 1 := by
    have h5 : Real.log x > Real.log (Real.exp 1) := by
      apply Real.log_lt_log
      all_goals
        linarith [Real.exp_pos 1, h1]
    have h6 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    linarith
  have h7 : Real.log y > 1 := by
    have h8 : Real.log y > Real.log (Real.exp 1) := by
      apply Real.log_lt_log
      all_goals
        linarith [Real.exp_pos 1, h2]
    have h9 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    linarith
  have h10 : x > 0 := by linarith [Real.exp_pos 1, h1]
  have h11 : y > 0 := by linarith [Real.exp_pos 1, h2]
  have h14 : Real.log x * y ≥ Real.log y * x := by
    have h17 : Real.log y ≤ Real.log x + (y - x) / x := by
      have h20 : Real.log (y / x) ≤ (y / x) - 1 := by
        apply Real.log_le_sub_one_of_pos
        positivity
      have h21 : Real.log (y / x) = Real.log y - Real.log x := by
        rw [Real.log_div (by positivity) (by positivity)]
      have h22 : Real.log y - Real.log x ≤ (y / x) - 1 := by linarith [h20, h21]
      have h23 : Real.log y ≤ Real.log x + (y - x) / x := by
        have h24 : (y / x) - 1 = (y - x) / x := by 
          field_simp
          all_goals linarith
        nlinarith [h22, h24]
      linarith
    have h18 : Real.log x * y ≥ Real.log y * x := by
      have h22 : Real.log x * (y - x) ≥ (y - x) := by
        have h25 : 0 ≤ y - x := by linarith
        have h26 : Real.log x ≥ 1 := by linarith
        nlinarith
      have h27 : Real.log x * y = Real.log x * x + Real.log x * (y - x) := by
        ring
      nlinarith [h17, show x * (Real.log x + (y - x) / x) = Real.log x * x + (y - x) by 
          field_simp
          all_goals nlinarith
        ]
    linarith
  have h15 : Real.log x / x ≥ Real.log y / y := by
    have h16 : 0 < x := by positivity
    have h17 : 0 < y := by positivity
    have h18 : Real.log x * y ≥ Real.log y * x := h14
    have h19 : Real.log x / x ≥ Real.log y / y := by
      have h20 : Real.log x * y ≥ Real.log y * x := h14
      have h21 : 0 < x * y := mul_pos (by positivity) (by positivity)
      have h22 : Real.log x / x - Real.log y / y ≥ 0 := by
        have h23 : Real.log x / x - Real.log y / y = (Real.log x * y - Real.log y * x) / (x * y) := by
          field_simp
          ring
        rw [h23]
        apply div_nonneg
        linarith
        positivity
      linarith
    exact h19
  have h18 : f x ≥ f y := by
    rw [hf]
    simp [h15]
  exact h18