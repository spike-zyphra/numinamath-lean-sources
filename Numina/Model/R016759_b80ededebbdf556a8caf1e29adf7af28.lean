import Mathlib

theorem algebra_15006 {f g : Polynomial ℤ} (hf : f.degree = 2)
    (hg : g.degree < f.degree) : (f + g).degree = 2 := by 
  have eq1 : g.degree < f.degree := by 
    rw [hf] at *
    exact_mod_cast hg
  have eq2 : (f + g).degree = f.degree := by 
    apply Polynomial.degree_add_eq_left_of_degree_lt
    exact_mod_cast eq1
  rw [eq2, hf]