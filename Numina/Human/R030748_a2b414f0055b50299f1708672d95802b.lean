import Mathlib

/- Let P be a cubic polynomial with P(0)=k, P(1)=2k, and P(−1)=3k. What is P(2)+P(−2) ?
(A) 0
(B) k
(C) 6k
(D) 7k
(E) 14k
-/
theorem algebra_96275 {P : Polynomial ℝ} (hP : P.degree = 3) (k : ℝ) (hP0 : P.eval 0 = k) (hP1 : P.eval 1 = 2 * k) (hP2 : P.eval (-1) = 3 * k) : P.eval 2 + P.eval (-2) = 14 * k := by
  -- express polynomial as ax^3 + bx^2 + cx + d first
  have hP' : ∀ x:ℝ, P.eval x = (P.coeff 0) + (P.coeff 1)*x + (P.coeff 2)*x^2 + (P.coeff 3)*x^3 := by
    nth_rw 1 [P.as_sum_range' 4]
    . intro x
      simp [Polynomial.eval_finset_sum, Finset.sum_range, Fin.sum_univ_four]
      norm_cast
    . rw [Polynomial.natDegree_eq_of_degree_eq_some hP]
      norm_num
  set a := P.coeff 3
  set b := P.coeff 2
  set c := P.coeff 1
  set d := P.coeff 0
  -- plug in 0 to get d = k, and then plug in 1 and -1 to get a+b+c+k=2k and -a+b-c+k=3k
  have habc₁ : d = k := by rw [hP' 0] at hP0; linarith
  rw [habc₁] at hP'
  have habc₂ : a + b + c + k = 2*k := by rw [hP'] at hP1; linarith
  have habc₃ : -a + b - c + k = 3*k := by rw [hP'] at hP2; linarith
  -- finally plug in 2 and -2 and use last 2 equation to eliminate b and get 14k
  rw [hP' 2, hP' (-2)]
  linarith