import Mathlib

theorem inequalities_241547 (P Q : ℤ) (hP : P^2 ≤ 729 ∧ 729 ≤ -P^3) (hQ : Q^2 ≤ 729 ∧ 729 ≤ -Q^3) :
    10 * (P - Q) ≤ 180 := by
  have hP1 : P^2 ≤ 729 := hP.1
  have hP2 : 729 ≤ -P^3 := hP.2
  have hQ1 : Q^2 ≤ 729 := hQ.1
  have hQ2 : 729 ≤ -Q^3 := hQ.2
  have h1 : -27 ≤ P := by
    nlinarith [sq_nonneg (P + 27), sq_nonneg (P - 27), hP1]
  have h2 : P ≤ -9 := by
    nlinarith [sq_nonneg (P + 9), sq_nonneg (P ^ 2), hP2]
  have h1' : -27 ≤ Q := by
    nlinarith [sq_nonneg (Q + 27), sq_nonneg (Q - 27), hQ1]
  have h2' : Q ≤ -9 := by
    nlinarith [sq_nonneg (Q + 9), sq_nonneg (Q ^ 2), hQ2]
  omega