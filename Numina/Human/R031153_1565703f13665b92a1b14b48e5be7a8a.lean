import Mathlib

open Polynomial Bivariate

/-
  The polynomial $x^{2}-3kxy-3y^{2}+6xy-8$ does not contain the term $xy$. Find the value of $k$.
-/
theorem algebra_9436 (k : ℝ) (p : ℝ[X][Y]) (hp : p = C X ^ 2 - C (C (3 * k) * X) * Y - 3 * Y ^ 2 +  C (6 * X) * Y - 8)
    (hp' : (p.coeff 1).coeff 1 = 0) : k = 2 := by
  -- compute coeff of xy
  have : coeff ((@C ℝ[X] _ X) ^ 2) 1 = 0 := by
    rw [<-C_pow]
    exact coeff_C_succ
  have : coeff p 1 = 6 * X - C (3 * k) * X := by
    simp [hp, this]
    ring
  -- simp
  simp [this] at hp'
  linarith
