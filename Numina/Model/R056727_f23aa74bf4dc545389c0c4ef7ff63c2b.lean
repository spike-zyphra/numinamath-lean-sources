import Mathlib

theorem algebra_2215 {A B A' B' : ℝ}
    (hA : A = -3) (hB : B = -1 / 2)
    (hA' : A' = B' - (B - A)) (hB'' : (A' + B') / 2 = 3) :
    A' = 7 / 4 ∧ dist A' A = 19 / 4 := by
  have h1 : A' + B' = 6 := by 
    linarith
  have h2 : B - A = 5 / 2 := by
    rw [hA, hB]
    norm_num
  have eq1 : A' = B' - (5 / 2) := by
    rw [hA']
    rw [h2]
    all_goals ring
  have hB' : B' = 17 / 4 := by 
    nlinarith [h1, eq1]
  have hA'2 : A' = 7 / 4 := by
    rw [hB'] at eq1 
    linarith
  have h3 : dist A' A = 19 / 4 := by
    rw [dist_eq_norm]
    rw [hA'2, hA]
    norm_num [abs_of_pos]
    all_goals norm_num
  constructor
  · linarith 
  · exact h3