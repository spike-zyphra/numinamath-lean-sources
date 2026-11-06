import Mathlib

theorem algebra_210366 {p : Polynomial ℤ} (hp : p.degree = 32)
    (h1 : p.coeff 1 = -2) (h2 : ∀ i ∈ Finset.Icc 2 32, p.coeff i = 0) :
    p.coeff 32 = 2^27 - 2^11 := by 
  have h232 := h2 32 (by norm_num)
  have h9 : p.natDegree = 32 := by 
    rw [Polynomial.natDegree_eq_of_degree_eq_some hp]
    all_goals norm_num 
    all_goals norm_num 
  have h10 : p.leadingCoeff = p.coeff 32 := by 
    rw [Polynomial.leadingCoeff, h9]
    all_goals norm_num 
  have h3 : p.leadingCoeff ≠ 0 := by 
    have h9 : p ≠ 0 := by 
      intro h 
      rw [h] at hp 
      simp at hp 
      all_goals norm_num at hp 
    by_contra h3
    have h4 : p.leadingCoeff = 0 := by 
      simp [h3]
    have h5 : p = 0 := by 
      apply Polynomial.leadingCoeff_eq_zero.mp 
      exact_mod_cast h4 
    contradiction 
  -- We now show that p.leadingCoeff must be zero, which is a contradiction 
  have h4 : p.leadingCoeff = 0 := by 
    linarith [show p.leadingCoeff = p.coeff 32 by exact_mod_cast h10, show p.coeff 32 = (0 : ℤ) by linarith [h232]]
  contradiction 
  all_goals norm_num 
  all_goals norm_num [h9, h232]