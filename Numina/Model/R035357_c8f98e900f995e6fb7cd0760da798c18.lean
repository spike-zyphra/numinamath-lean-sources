import Mathlib
open Polynomial

theorem algebra_21959 {f g : Polynomial ℝ} (hf : f = 3 * X ^ 4 + 5 * X ^ 2 - 9 * X - 2)
    (hg : g = f.comp (X - 1)) : ∑ i in Finset.Icc 0 g.natDegree, g.coeff i = -2 := by 
  have h1 : ∑ i in Finset.Icc 0 g.natDegree, g.coeff i = g.eval 1 := by 
    rw [Polynomial.eval_eq_sum_range]
    have h2 : Finset.range (g.natDegree + 1) = Finset.Icc 0 g.natDegree := by 
      ext i
      simp
      <;> omega
    rw [h2]
    all_goals norm_num
    all_goals ring
  have h2 : g.eval 1 = f.eval 0 := by 
    rw [hg]
    simp [Polynomial.eval_comp]
  have h3 : f.eval 0 = -2 := by
    rw [hf]
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [h1]
  rw [h2]
  rw [h3]