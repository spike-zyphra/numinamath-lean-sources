import Mathlib

open Polynomial

theorem calculus_22298 (u v w : ℂ) (hroots : (X ^ 3 - 1 : ℂ[X]).roots = {u, v, w}) :
    u * v + u * w + v * w = 0 := by
  -- Set p := X^3 - 1 be the complex polynomial.
  set p : ℂ[X] := X ^ 3 - 1 with hp
  -- The polynomial has degree 3.
  have hdeg : p.natDegree = 3 := by
    rw [hp]
    compute_degree!
  -- The polynomial has as many roots as its degree.
  have hcard : p.roots.card = p.natDegree := by
    rw [hp, hroots]
    simp [← hp, hdeg]
  -- The leading coefficient is 1.
  have hcoeff : p.leadingCoeff = 1 := by
    rw [hp, ← coeff_natDegree, hdeg]
    simp [coeff_one]
  -- Use Vieta's formula for the coefficient of X.
  -- We have uv + uw + vw = 0.
  have H := coeff_eq_esymm_roots_of_card hcard (k := 1) (by simp [hdeg])
  simp [hcoeff, hdeg, hroots, Multiset.esymm, Multiset.powersetCard_one] at H
  -- Simplify the expression and we are done.
  simp [hp, coeff_one] at H
  linear_combination -H
