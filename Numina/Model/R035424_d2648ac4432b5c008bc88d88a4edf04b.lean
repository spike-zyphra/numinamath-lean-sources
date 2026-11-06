import Mathlib

open Polynomial

theorem algebra_11860 {P : Polynomial ℝ} (hP : ∀ x, P.eval x = P.eval 0 + P.eval 1 * x + P.eval 2 * x ^ 2)
    (hP' : P.eval (-1) = 1) :
    P = X ^ 2 - X - 1 := by
  have eq1 := hP (-1)
  have eq2 := hP 0
  have eq3 := hP 1
  have eq4 := hP 2
  simp [hP'] at eq1
  simp at eq2 eq3 eq4
  have eq5 : P.eval 0 = -1 := by
    nlinarith
  have eq6 : P.eval 1 = -1 := by
    nlinarith
  have eq7 : P.eval 2 = 1 := by
    nlinarith
  apply Polynomial.funext
  intro x
  have eq8 : P.eval x = -1 + (-1) * x + 1 * x ^ 2 := by
    have h1 := hP x
    simp [eq5, eq6, eq7] at h1 ⊢
    linarith
  simp [eq8]
  <;> ring