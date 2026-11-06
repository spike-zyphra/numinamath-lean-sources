import Mathlib

open Polynomial

/-Rewrite the expression $6j^2 - 4j + 12$ in the form $c(j + p)^2 + q$, where $c$, $p$, and $q$ are constants. What is $\frac{q}{p}$?

The final answer is $ \boxed{-34} $-/
theorem algebra_10695 {c p q : ℝ} (h : (6 : ℝ) • X ^ 2 - 4 * X + 12 = c •  (X + C p) ^ 2 + C q) :
  q / p = -34 := by
    ring_nf at h
    simp [smul_add] at h
    -- Because (6 : ℝ) • X ^ 2 - 4 * X + 12 = c •  (X + C p) ^ 2 + C q), we have the coeffs of the are same.
    -- So we get three equation about $c, p, q$.
    have h2 := Polynomial.ext_iff.1 h 2
    have h1 := Polynomial.ext_iff.1 h 1
    have h0 := Polynomial.ext_iff.1 h 0
    -- Solve the equations we get $p = -1 / 3$ and $q = 34 / 3$.
    simp at h2 h1 h0
    rw [ ←Polynomial.C_pow, Polynomial.coeff_C] at h1 h2 h0
    simp at h1 h2 h0
    simp [Polynomial.coeff_X] at h2
    simp [←h2] at h0 h1
    have hp : p = - 1  / 3 := by nlinarith
    simp [hp] at h0
    have hq : q = 34 / 3 := by ring_nf at h0; linarith
    -- so $q / p = -34$
    simp [hp, hq]
    ring
