import Mathlib


theorem algebra_168448 {f g : ℝ → ℝ} (hf : ∀ x, f x = x^3 + 3 * x^2 + 5 * x + 7)
    (hg : ∃ p : Polynomial ℝ, p.degree = 2 ∧ ∀ x, g x = p.eval x)
    (h1 : f 3 = g 3) (h2 : f (3 - Real.sqrt 3) = g (3 - Real.sqrt 3)) (h3 : f (3 + Real.sqrt 3) = g (3 + Real.sqrt 3)) :
    g = fun x => 12 * x^2 - 19 * x + 25 := by

  rcases hg with ⟨p, hp2, hgp⟩

  have h4 : p.natDegree = 2 := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hp2]

  have eq1' : p.eval 3 = (p.coeff 2) * (3:ℝ) ^ 2 + (p.coeff 1) * (3:ℝ) + (p.coeff 0) := by
    simp [Polynomial.eval_eq_sum_range, h4, Finset.sum_range_succ, pow_two, pow_zero, mul_add, mul_assoc]
    all_goals ring

  have eq2' : p.eval (3 - Real.sqrt 3) = (p.coeff 2) * (3 - Real.sqrt 3:ℝ) ^ 2 + (p.coeff 1) * (3 - Real.sqrt 3:ℝ) + (p.coeff 0) := by
    simp [Polynomial.eval_eq_sum_range, h4, Finset.sum_range_succ, pow_two, pow_zero, mul_add, mul_assoc]
    all_goals ring

  have eq3' : p.eval (3 + Real.sqrt 3) = (p.coeff 2) * (3 + Real.sqrt 3:ℝ) ^ 2 + (p.coeff 1) * (3 + Real.sqrt 3:ℝ) + (p.coeff 0) := by
    simp [Polynomial.eval_eq_sum_range, h4, Finset.sum_range_succ, pow_two, pow_zero, mul_add, mul_assoc]
    all_goals ring


  have eq1 := h1
  rw [hf, hgp] at eq1
  rw [eq1'] at eq1

  have eq2 := h2
  rw [hf, hgp] at eq2
  rw [eq2'] at eq2

  have eq3 := h3
  rw [hf, hgp] at eq3
  rw [eq3'] at eq3

  have eq1_1 : (p.coeff 2) * 9 + (p.coeff 1) * 3 + (p.coeff 0) = 76 := by
    norm_num at eq1
    linarith

  have eq2_1 : (p.coeff 2) * (3 - Real.sqrt 3:ℝ) ^ 2 + (p.coeff 1) * (3 - Real.sqrt 3:ℝ) + (p.coeff 0) = (3 - Real.sqrt 3)^3 + 3 * (3 - Real.sqrt 3)^2 + 5 * (3 - Real.sqrt 3) + 7 := by
    linarith

  have eq3_1 : (p.coeff 2) * (3 + Real.sqrt 3:ℝ) ^ 2 + (p.coeff 1) * (3 + Real.sqrt 3:ℝ) + (p.coeff 0) = (3 + Real.sqrt 3)^3 + 3 * (3 + Real.sqrt 3)^2 + 5 * (3 + Real.sqrt 3) + 7 := by
    linarith

  have eq5 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  have eq6 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    calc
      Real.sqrt 3 ^ 3 = (Real.sqrt 3 ^ 2) * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  ring_nf at eq2_1 eq3_1
  norm_num [eq5, eq6] at eq2_1 eq3_1

  have h9 : (p.coeff 2) = 12 := by
    nlinarith [sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  have h10 : (p.coeff 1) = -19 := by
    nlinarith [sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  have h11 : (p.coeff 0) = 25 := by
    linarith

  funext x
  have eq7 : g x = p.eval x := hgp x
  rw [eq7]
  simp [Polynomial.eval_eq_sum_range, h4, Finset.sum_range_succ, pow_two, pow_zero, mul_add, mul_assoc, h9, h10, h11]
  all_goals ring