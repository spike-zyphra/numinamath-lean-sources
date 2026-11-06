import Mathlib

theorem algebra_96275 {P : Polynomial ℝ} (hP : P.degree = 3) (k : ℝ) (hP0 : P.eval 0 = k) (hP1 : P.eval 1 = 2 * k) (hP2 : P.eval (-1) = 3 * k) : P.eval 2 + P.eval (-2) = 14 * k := by
  have h2 : P.natDegree = 3 := by 
    rw [Polynomial.natDegree_eq_of_degree_eq_some hP]
  have h3 : ∀ x: ℝ, P.eval x = 
    (P.coeff 3) * x ^ 3 + (P.coeff 2) * x ^ 2 + (P.coeff 1) * x + (P.coeff 0) := by
    intro x 
    simp [Polynomial.eval_eq_sum_range, h2, Finset.sum_range_succ, mul_comm]
    <;> ring
  set a := P.coeff 3 with ha
  set b := P.coeff 2 with hb
  set c := P.coeff 1 with hc
  set d := P.coeff 0 with hd
  have h0 : a * (0 : ℝ) ^ 3 + b * (0 : ℝ) ^ 2 + c * (0 : ℝ) + d = k := by 
    specialize h3 0 
    rw [h3] at hP0 
    linarith
  have h00 : d = k := by 
    linarith
  have h1 : a * (1 : ℝ) ^ 3 + b * (1 : ℝ) ^ 2 + c * (1 : ℝ) + d = 2 * k := by 
    specialize h3 1 
    rw [h3] at hP1 
    linarith
  have h11 : a + b + c + d = 2 * k := by 
    linarith
  have h_1 : a * (-1 : ℝ) ^ 3 + b * (-1 : ℝ) ^ 2 + c * (-1 : ℝ) + d = 3 * k := by 
    specialize h3 (-1) 
    rw [h3] at hP2 
    linarith
  have h_11 : -a + b - c + d = 3 * k := by 
    linarith
  have h4 : P.eval 2 = a * (2 : ℝ) ^ 3 + b * (2 : ℝ) ^ 2 + c * (2 : ℝ) + d := by 
    specialize h3 2 
    linarith
  have h5 : P.eval (-2: ℝ) = a * (-2: ℝ) ^ 3 + b * (-2: ℝ) ^ 2 + c * (-2: ℝ) + d := by 
    specialize h3 (-2: ℝ) 
    linarith
  have h6 : b = 3 * k / 2 := by 
    nlinarith [h00, h11, h_11]
  rw [h4, h5]
  rw [h00]
  linarith [h6]