import Mathlib

theorem algebra_1464 (f g : Polynomial ℝ) (hf : f.degree = 10) (hg : g.degree = 10) :
    (f + g).degree ≤ 10 := by
  have h1 : (f + g).degree ≤ max f.degree g.degree := by 
    apply Polynomial.degree_add_le
  have h3 : max f.degree g.degree = 10 := by 
    rw [hf, hg]
    all_goals norm_num
  have h4 : (f + g).degree ≤ 10 := by
    rw [h3] at h1
    exact_mod_cast h1
  exact h4