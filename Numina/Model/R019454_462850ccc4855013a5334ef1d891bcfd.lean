import Mathlib

theorem algebra_18711 {f g : Polynomial ℝ} (hf : f.degree = 4) (hg : g.degree = 2) :
    (f - g).degree = 4 := by
  have h2 : f.degree = 4 := hf
  have h3 : g.degree = 2 := hg
  have h4 : g.degree < f.degree := by 
    rw [h2, h3]
    all_goals norm_num 
  have h5 : (f - g).degree = f.degree := by 
    apply Polynomial.degree_sub_eq_left_of_degree_lt 
    all_goals 
      try exact_mod_cast h4 
  rw [h5, h2]
  all_goals 
    try norm_num