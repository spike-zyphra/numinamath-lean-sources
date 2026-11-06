import Mathlib

open Real

theorem algebra_11266 {E : ℝ → ℝ} (hE : E = fun x => sqrt (abs (x + 1)) + (9 / π) * arctan (sqrt (abs x))) :
    E 3 = 5 := by 
  rw [hE]
  have h1 : sqrt (abs (3 + 1 : ℝ)) = 2 := by
    have h2 : abs (3 + 1 : ℝ) = 4 := by 
      norm_num [abs_of_nonneg]
    rw [h2]
    rw [show sqrt (4 : ℝ) = 2 by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    ]
  have h2' : sqrt (abs (3 : ℝ)) = sqrt 3 := by
    norm_num [abs_of_nonneg]
  have h4 : arctan (sqrt (abs (3 : ℝ))) = Real.pi / 3 := by 
    rw [h2']
    have h5 : arctan (sqrt 3) = Real.pi / 3 := by 
      have h6 : arctan (tan (Real.pi / 3)) = Real.pi / 3 := by 
        rw [Real.arctan_tan]
        all_goals linarith [Real.pi_pos]
      have h5' : sqrt 3 = tan (Real.pi / 3) := by
        have htan : tan (Real.pi / 3) = sqrt 3 := by 
          exact tan_pi_div_three
        linarith [htan]
      rw [h5']
      exact h6
    exact_mod_cast h5
  simp only [h1, h4]
  field_simp
  <;> linarith