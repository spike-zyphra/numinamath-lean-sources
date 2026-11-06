import Mathlib

theorem algebra_258794 (P : ℝ → ℝ) (hP : P 0 = 1) (hP' : ∀ n, P (n + 6) = 3 * P n) :
    ∃ n, P n = 81 := by 
  have eq1 : P 6 = 3 * P 0 := by 
    specialize hP' 0
    norm_num at hP' ⊢
    all_goals linarith [hP']
  have eq2 : P 6 = 3 := by 
    rw [show P 0 = (1 : ℝ) by linarith [hP] ] at eq1
    linarith 
  have eq3 : P 12 = 3 * P 6 := by 
    specialize hP' 6 
    norm_num at hP' ⊢
    exact hP'
  have eq4 : P 12 = 9 := by 
    rw [eq2] at eq3 
    linarith 
  have eq5 : P 18 = 3 * P 12 := by
    specialize hP' 12 
    norm_num at hP' ⊢
    exact hP'
  have eq6 : P 18 = 27 := by
    rw [eq4] at eq5 
    linarith
  have eq7 : P 24 = 3 * P 18 := by
    specialize hP' 18 
    norm_num at hP' ⊢
    exact hP'
  have eq8 : P 24 = 81 := by 
    rw [eq6] at eq7 
    linarith
  use 24 
  all_goals 
    norm_num [eq8]