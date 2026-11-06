import Mathlib

theorem algebra_158150 {P : Polynomial ℝ} (hP : P.degree ≤ 3)
    (hP1 : P.eval 1 = 1 / (1 + 1 + 1 ^ 2)) (hP2 : P.eval 2 = 1 / (1 + 2 + 2 ^ 2))
    (hP3 : P.eval 3 = 1 / (1 + 3 + 3 ^ 2)) (hP4 : P.eval 4 = 1 / (1 + 4 + 4 ^ 2)) :
    P.eval 5 = -3 / 91 := by
  have h1 : P.natDegree ≤ 3 := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact hP
  have eq1 : P.eval 1 = 1 / 3 := by
    norm_num at hP1 ⊢
    linarith
  have eq2 : P.eval 2 = 1 / 7 := by
    norm_num at hP2 ⊢
    linarith
  have eq3 : P.eval 3 = 1 / 13 := by
    norm_num at hP3 ⊢
    linarith
  have eq4 : P.eval 4 = 1 / 21 := by
    norm_num at hP4 ⊢
    linarith
  have eq9 : ∀ (x : ℝ), P.eval x = P.coeff 0 + P.coeff 1 * x + P.coeff 2 * x ^ 2 + P.coeff 3 * x ^ 3 := by
    intro x
    rw [Polynomial.eval_eq_sum_range' (show P.natDegree < 4 by omega)]
    simp [Finset.sum_range_succ, pow_succ, mul_assoc]
    <;> ring_nf 
  -- building four equations.
  have eq10 := eq9 1
  rw [eq1] at eq10
  -- building four equations.
  have eq11 := eq9 2
  rw [eq2] at eq11
  -- building four equations.
  have eq12 := eq9 3
  rw [eq3] at eq12
  -- building four equations.
  have eq13 := eq9 4
  rw [eq4] at eq13
  have eq14 : P.eval 5 = P.coeff 0 + P.coeff 1 * (5 : ℝ) + P.coeff 2 * (5 : ℝ) ^ 2 + P.coeff 3 * (5 : ℝ) ^ 3 := by
    apply eq9
  norm_num at eq10 eq11 eq12 eq13 eq14
  linarith