import Mathlib

theorem algebra_189125 {f : ℝ → ℝ} (hf : ∃ p : Polynomial ℝ, p.degree ≤ 2 ∧ ∀ x, f x = p.eval x)
    (h0 : f 0 = 1) (h1 : f 1 = 3) (h2 : f 2 = 3) :
    f = fun x => -x^2 + 3 * x + 1 := by 
  rcases hf with ⟨p, hp_degree, hp_eval⟩
  funext x
  have eq1 := hp_eval 0
  rw [h0] at eq1
  have eq2 := hp_eval 1
  rw [h1] at eq2
  have eq3 := hp_eval 2
  rw [h2] at eq3
  have eq6 : f x = p.eval x := hp_eval x
  rw [eq6]
  have eq10 : p.natDegree ≤ 2 := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact hp_degree
  have eq11 : p.eval 0 = 1 := by
    linarith [eq1]
  have eq12 : p.eval 1 = 3 := by
    linarith [eq2]
  have eq13 : p.eval 2 = 3 := by
    linarith [eq3]
  have eq14 : p.eval 0 = p.coeff 0 := by
    simp [Polynomial.eval]
  have eq15 : p.eval 1 = p.coeff 0 + p.coeff 1 * 1 + p.coeff 2 * 1^2 := by 
    rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 3 by 
      have : p.natDegree ≤ 2 := eq10
      omega
    )]
    simp [Finset.sum_range_succ, pow_one, pow_two]
    <;> ring
  have eq16 : p.eval 2 = p.coeff 0 + p.coeff 1 * 2 + p.coeff 2 * (2:ℝ)^2 := by 
    rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 3 by 
      have : p.natDegree ≤ 2 := eq10
      omega
    )]
    simp [Finset.sum_range_succ, pow_one, pow_two]
    <;> ring
  have eq17 : p.coeff 0 = 1 := by
    rw [eq14] at eq11
    linarith
  have eq18 : p.coeff 2 = -1 := by
    nlinarith [eq12, eq13, eq15, eq16, eq17, eq14]
  have eq19 : p.coeff 1 = 3 := by 
    nlinarith [eq12, eq13, eq15, eq16, eq17, eq14, eq18]
  have eq20 : p.eval x = p.coeff 0 + p.coeff 1 * x + p.coeff 2 * x^2 := by 
    rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 3 by 
      have : p.natDegree ≤ 2 := eq10
      omega
    )]
    simp [Finset.sum_range_succ, pow_one, pow_two]
    <;> ring
  rw [eq20]
  rw [eq17, eq19, eq18]
  ring