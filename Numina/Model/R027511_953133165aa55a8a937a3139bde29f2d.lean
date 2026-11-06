import Mathlib

theorem algebra_58558 {P : Polynomial ℝ} (hP : P.degree = 3)
    (hP0 : P.eval 0 = 1) (hP1 : P.eval 1 = 3) (hP3 : P.eval 3 = 10) :
    P.eval 2 ≠ 6 := by
  have h1 : P.natDegree = 3 := by 
    rw [Polynomial.natDegree_eq_of_degree_eq_some hP]
    all_goals linarith
  have eq0 : P.eval 0 = 1 := hP0
  have eq1 : P.eval 1 = 3 := hP1
  have eq3 : P.eval 3 = 10 := hP3
  -- writing P(2) in terms of coefficients
  have eq4 : P.eval 2 = P.coeff 0 + 2 * (P.coeff 1) + 4 * (P.coeff 2) + 8 * (P.coeff 3) := by
    simp [Polynomial.eval_eq_sum_range, h1, Finset.sum_range_succ]
    <;> ring_nf 
    <;> norm_num 
    all_goals ring_nf 
  -- Assume P(2) = 6 for contradiction
  intro hcontr 
  -- This implies
  have eq5 : P.coeff 0 + 2 * (P.coeff 1) + 4 * (P.coeff 2) + 8 * (P.coeff 3) - 6 = 0 := by
    linarith [eq4, hcontr]
  -- It is needed to properly compute the value of c_0
  have eq00 : P.eval 0 = P.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, h1, Finset.sum_range_succ]
    all_goals norm_num 
    all_goals ring_nf
  have eq01 : P.coeff 0 = 1 := by 
    linarith [eq00, eq0]
  -- writing equations in terms of coefficients
  have eq11 : P.eval 1 = P.coeff 0 + P.coeff 1 + P.coeff 2 + P.coeff 3 := by
    simp [Polynomial.eval_eq_sum_range, h1, Finset.sum_range_succ]
    all_goals ring_nf
    all_goals norm_num 
    all_goals ring_nf
  -- getting sum c_0 + c_1 + c_2 + c_3 = 3
  have eq2 : P.coeff 0 + P.coeff 1 + P.coeff 2 + P.coeff 3 = 3 := by 
    linarith [eq11, eq1]
  -- writing equations in terms of coefficients for P 3
  have eq33 : P.eval 3 = P.coeff 0 + 3 * P.coeff 1 + 9 * P.coeff 2 + 27 * P.coeff 3 := by
    simp [Polynomial.eval_eq_sum_range, h1, Finset.sum_range_succ]
    all_goals ring_nf
    all_goals norm_num
    all_goals ring_nf 
  -- getting sum c_0 + 3c_1 + 9c_2 + 27c_3 = 10
  have eq44 : P.coeff 0 + 3 * P.coeff 1 + 9 * P.coeff 2 + 27 * P.coeff 3 = 10 := by
    linarith [eq33, eq3]
  -- Now to solve a system of linear equations...
  have eq6 : P.leadingCoeff = P.coeff 3 := by 
    rw [Polynomial.leadingCoeff]
    rw [h1]
    all_goals simp 
  have hc3 : P.coeff 3 = P.leadingCoeff := by 
    rw [eq6]
    <;> try tauto 
  -- leading coefficient P is non zero because degree P is 3
  have hc4 : P.leadingCoeff ≠ 0 := by 
    have h5 : P ≠ 0 := by
      intro h
      have h6 : P.eval 1 = (0 : ℝ) := by
        simp [h]
      linarith [hP1, h6]
    have h7 : P.leadingCoeff ≠ 0 := by
      by_contra h
      have h8 : P.leadingCoeff = 0 := by
        exact h 
      -- Since leading coeff is zero, which given polynomial degree exactly 3 is a contradiction
      have h2 : P = 0 := by 
        apply Polynomial.leadingCoeff_eq_zero.mp 
        simpa using h8 
      contradiction 
      all_goals nlinarith 
    assumption 
  -- solving the system of equations to get c_3 = 0
  have h3 : P.coeff 3 = 0 := by 
    nlinarith [sq_nonneg (P.coeff 1), sq_nonneg (P.coeff 2), sq_nonneg (P.coeff 3), eq01, eq2, eq44]
  -- contradiction
  have h4 : (P : Polynomial ℝ).leadingCoeff = 0 := by
    rw [← hc3]
    all_goals linarith 
  have h5 : (P : Polynomial ℝ).leadingCoeff ≠ 0 := hc4 
  contradiction