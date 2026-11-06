import Mathlib
open Polynomial

/- The three roots of the cubic $ 30 x^3 - 50x^2 + 22x - 1$ are distinct real numbers strictly between $ 0$ and $ 1$.  If the roots are $p$, $q$, and $r$, what is the sum
\[ \frac{1}{1-p} + \frac{1}{1-q} +\frac{1}{1-r} ?\] -/
theorem algebra_12601 {p q r : ℝ} (h : (30 * X^3 - 50 * X^2 + 22 * X - 1 : ℝ[X]).roots = [p, q, r]) (hp : 0 < p ∧ p < 1) (hq : 0 < q ∧ q < 1) (hr : 0 < r ∧ r < 1) : 1 / (1 - p) + 1 / (1 - q) + 1 / (1 - r) = 12 := by
  -- Set the polynomial as p
  let f : ℝ[X] := 30 * X^3 - 50 * X^2 + 22 * X - 1
  -- Compute the coefficients of p
  have f0 : f.coeff 0 = -1 := by simp [f]
  have f1 : f.coeff 1 = 22 := by simp [f, coeff_one]
  have f2 : f.coeff 2 = -50 := by simp [f, Polynomial.coeff_X_of_ne_one, coeff_one]
  have f3 : f.coeff 3 = 30 := by simp [f, Polynomial.coeff_X_of_ne_one, coeff_one]
  -- Compute the degree of p
  have f4 : f.natDegree = 3 := by
    simp [f]
    have : (30 * X ^ 3 - 50 * X ^ 2 + 22 * X - 1 : ℝ[X]) = (C 30 * X ^ 3 + C (-50) * X ^ 2 + C 22 * X + C (-1)) := by
      simp
      have k0 : (30 : ℝ[X]) = C 30 := by
        rw [show (30 : ℝ) = (30 : ℕ) by simp, C_eq_natCast]
        simp
      have k1 : (50 : ℝ[X]) = C 50 := by
        rw [show (50 : ℝ) = (50 : ℕ) by simp, C_eq_natCast]
        simp
      have k2 : (22 : ℝ[X]) = C 22 := by
        rw [show (22 : ℝ) = (22 : ℕ) by simp, C_eq_natCast]
        simp
      have k3 : (1 : ℝ[X]) = C 1 := by
        rw [show (1 : ℝ) = (1 : ℕ) by simp, C_eq_natCast]
        simp
      rw [k0, k1, k2, k3]
      ring
    rw [this]
    exact natDegree_cubic (by norm_num)
  -- Compute the leading coefficient of p
  have f5 : f.leadingCoeff = 30 := by
    rw [← Polynomial.coeff_natDegree, f4, f3]

  -- 1 - p ≠ 0, 1 - q ≠ 0, 1 - r ≠ 0 from the given conditions
  replace hp : 1 - p ≠ 0 := by linarith only [hp.2]
  replace hq : 1 - q ≠ 0 := by linarith only [hq.2]
  replace hr : 1 - r ≠ 0 := by linarith only [hr.2]

  -- Vieta's formulas:
  -- p + q + r = 50 / 30
  -- p * q + q * r + r * p = 22 / 30
  -- p * q * r = 1 / 30
  have ⟨h1, h2, h3⟩ : p + q + r = 50 / 30 ∧ p * q + q * r + r * p = 22 / 30 ∧ p * q * r = 1 / 30 := by
    -- Vieta's formulas
    have h1 := coeff_eq_esymm_roots_of_card (p := f)
    simp [h, f4] at h1
    refine ⟨?_, ?_, ?_⟩
    . specialize h1 (show 2 ≤ 3 by simp)
      simp [f2, f5, Multiset.esymm, Multiset.powersetCard] at h1
      linarith only [h1]
    . specialize h1 (show 1 ≤ 3 by simp)
      simp [f1, f5, Multiset.esymm, Multiset.powersetCard] at h1
      linarith only [h1]
    . specialize h1 (show 0 ≤ 3 by simp)
      simp [f0, f5, Multiset.esymm, Multiset.powersetCard] at h1
      linarith only [h1]

  -- Simplify the expression
  -- 1 / (1 - p) + 1 / (1 - q) + 1 / (1 - r) = ((1 - p) * (1 - q) + (1 - q) * (1 - r) + (1 - r) * (1 - p)) / ((1 - p) * (1 - q) * (1 - r))
  have k1 : 1 / (1 - p) + 1 / (1 - q) + 1 / (1 - r) = ((1 - p) * (1 - q) + (1 - q) * (1 - r) + (1 - r) * (1 - p)) / ((1 - p) * (1 - q) * (1 - r)) := by
    field_simp [hp, hq, hr]
    ring
  rw [k1]

  -- Rewrite the numerator and the denominator with fundamental symmetric polynomials
  rw [show (1 - p) * (1 - q) + (1 - q) * (1 - r) + (1 - r) * (1 - p) = (p * q + q * r + r * p) - 2 * (p + q + r) + 3 by ring]
  rw [show (1 - p) * (1 - q) * (1 - r) = 1 - (p + q + r) + (p * q + q * r + r * p) - p * q * r by ring]

  -- Substitute the values of the symmetric polynomials
  rw [h1, h2, h3]
  norm_num
