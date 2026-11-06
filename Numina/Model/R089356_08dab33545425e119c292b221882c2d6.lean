import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11613 {f : ℝ → ℝ} (hf : f = λ x => logb (1/2) (-x^2 - 2*x + 3)) :
    StrictMonoOn f (Ico (-1) 1) := by
  rw [hf]
  intro x hx y hy hxy
  have hx1 : -1 ≤ x := hx.1
  have hx2 : x < 1 := hx.2
  have hy1 : -1 ≤ y := hy.1
  have hy2 : y < 1 := hy.2
  have hxy' : x < y := hxy
  have h1 : -x^2 - 2*x + 3 > 0 := by
    nlinarith
  have h2 : -y^2 - 2*y + 3 > 0 := by
    nlinarith
  have h3 : -x^2 - 2*x + 3 > (-y^2 - 2*y + 3) := by 
    have h5 : (y - x) * (y + x + 2) > 0 := by
      have y_sub_x_pos : y - x > 0 := by linarith
      have y_add_x_add_2_pos : y + x + 2 > 0 := by 
        nlinarith 
      nlinarith 
    nlinarith 
  have h4 : logb (1 / 2) (-x^2 - 2*x + 3) < logb (1 / 2) (-y^2 - 2*y + 3) := by 
    apply logb_lt_logb_of_base_lt_one 
    all_goals nlinarith
  exact h4