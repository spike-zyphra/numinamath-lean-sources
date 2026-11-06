import Mathlib

open Real

theorem algebra_9483 {e1 e2 : ℝ × ℝ} (he1 : e1.1^2 + e1.2^2 = 1) (he2 : e2.1^2 + e2.2^2 = 1)
    (hangle : arccos (e1.1 * e2.1 + e1.2 * e2.2) = π / 3) (Q : ℝ × ℝ) (hQ : Q.1 = 2 * e1.1 + 1 * e2.1)
    (hQ' : Q.2 = 2 * e1.2 + 1 * e2.2) :
    Real.sqrt (Q.1^2 + Q.2^2) = Real.sqrt 7 := by
  have he1e2dot : e1.1 * e2.1 + e1.2 * e2.2 = 1 / 2 := by 
    have hcos : e1.1 * e2.1 + e1.2 * e2.2 = Real.cos (π / 3) := by 
      have eq1 : arccos (e1.1 * e2.1 + e1.2 * e2.2) = π / 3 := hangle 
      have eq2 : Real.cos (arccos (e1.1 * e2.1 + e1.2 * e2.2)) = e1.1 * e2.1 + e1.2 * e2.2 := by 
        have h1a : (e1.1 * e2.1 + e1.2 * e2.2) ≥ -1 := by 
          nlinarith [ sq_nonneg (e1.1 - e2.1), sq_nonneg (e1.2 - e2.2), sq_nonneg (e1.1 + e2.1), sq_nonneg (e1.2 + e2.2), sq_nonneg (e1.1 - e2.1), sq_nonneg (e1.2 - e2.2) ]
        have h1b : (e1.1 * e2.1 + e1.2 * e2.2) ≤ 1 := by 
          nlinarith [ sq_nonneg (e1.1 - e2.1), sq_nonneg (e1.2 - e2.2), sq_nonneg (e1.1 + e2.1), sq_nonneg (e1.2 + e2.2), sq_nonneg (e1.1 - e2.1), sq_nonneg (e1.2 - e2.2) ]
        rw [Real.cos_arccos h1a h1b]
      have eq3 : Real.cos (π / 3) = 1 / 2 := by 
        exact Real.cos_pi_div_three 
      have eq4 : Real.cos (arccos (e1.1 * e2.1 + e1.2 * e2.2)) = Real.cos (π / 3) := by 
        rw [eq1]

      linarith [eq2, eq3, eq4]

    have eq4 : Real.cos (π / 3) = 1 / 2 := by 
      exact Real.cos_pi_div_three 
    rw [eq4] at hcos 
    linarith [hcos]

  have hQ1 : Q.1 ^ 2 + Q.2 ^ 2 = 7 := by 
    rw [hQ, hQ']
    nlinarith [ he1, he2, he1e2dot, Real.cos_pi_div_three ]

  rw [hQ1]