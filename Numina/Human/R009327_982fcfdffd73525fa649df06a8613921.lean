import Mathlib
open Polynomial

/- Let $r$, $s$, and $t$ be the three roots of the equation $$
8x^3 + 1001x + 2008 = 0.
$$Find $(r + s)^3 + (s + t)^3 + (t + r)^3.$ -/
theorem algebra_16658 (r s t : ℂ) (h : (8 * X^3 + 1001 * X + 2008 : ℂ[X]).roots = [r, s, t]) : (r + s)^3 + (s + t)^3 + (t + r)^3 = 753 := by
  -- Set the polynomial as p
  let p : ℂ[X] := 8 * X^3 + 1001 * X + 2008
  -- Compute the coefficients of p
  have p0 : p.coeff 0 = 2008 := by simp [p]
  have p1 : p.coeff 1 = 1001 := by simp [p]
  have p2 : p.coeff 2 = 0 := by simp [p, Polynomial.coeff_X_of_ne_one]
  have p3 : p.coeff 3 = 8 := by simp [p, Polynomial.coeff_X_of_ne_one]
  -- Compute the degree of p
  have p4 : p.natDegree = 3 := by
    simp [p]
    have : (8 * X ^ 3 + 1001 * X + 2008 : ℂ[X]) = (C 8 * X ^ 3 + C 0 * X ^ 2 + C 1001 * X + C 2008) := by
      simp
      have k1 : (8 : ℂ[X]) = C 8 := by
        rw [show (8 : ℂ) = (8 : ℕ) by simp, C_eq_natCast]
        simp
      have k2 : (1001 : ℂ[X]) = C 1001 := by
        rw [show (1001 : ℂ) = (1001 : ℕ) by simp, C_eq_natCast]
        simp
      have k3 : (2008 : ℂ[X]) = C 2008 := by
        rw [show (2008 : ℂ) = (2008 : ℕ) by simp, C_eq_natCast]
        simp
      rw [k1, k2, k3]
    rw [this]
    exact natDegree_cubic (by norm_num)
  -- Compute the leading coefficient of p
  have p5 : p.leadingCoeff = 8 := by
    rw [← Polynomial.coeff_natDegree, p4, p3]
  -- p ≠ 0
  have p6 : p ≠ 0 := by
    intro hp
    rw [hp] at p0
    simp at p0

  -- The roots satisfy the equation
  have hr : 8 * r^3 + 1001 * r + 2008 = 0 := by
    have k := mem_roots_iff_aeval_eq_zero (x := r) p6
    simp [h, p] at k
    exact k

  have hs : 8 * s^3 + 1001 * s + 2008 = 0 := by
    have k := mem_roots_iff_aeval_eq_zero (x := s) p6
    simp [h, p] at k
    exact k

  have ht : 8 * t^3 + 1001 * t + 2008 = 0 := by
    have k := mem_roots_iff_aeval_eq_zero (x := t) p6
    simp [h, p] at k
    exact k

  -- r + s + t = 0 by Vieta's formulas
  have h1 : r + s + t = 0 := by
    -- Vieta's formulas
    have h1 := coeff_eq_esymm_roots_of_card (p := p)
    simp [h, p4] at h1
    specialize h1 (show 2 ≤ 3 by simp)
    -- Simplify esymm
    simp [p2, p6, Multiset.esymm, Multiset.powersetCard] at h1
    rw [← h1]
    ac_rfl

  -- Change r + s to -t, s + t to -r, and t + r to -s
  rw [show r + s = -t by rw [← sub_eq_zero, ← h1]; ring, show s + t = -r by rw [← sub_eq_zero, ← h1]; ring, show t + r = -s by rw [← sub_eq_zero, ← h1]; ring]
  rw [show (-t) ^ 3 + (-r) ^ 3 + (-s) ^ 3 = - (r ^ 3 + s ^ 3 + t^3) by ring]
  -- Change r^3, s^3, and t^3 to (-1001 * r - 2008) / 8, (-1001 * s - 2008) / 8, and (-1001 * t - 2008) / 8
  replace hr : r^3 = (-1001 * r - 2008) / 8 := by
    cancel_denoms
    rw [← sub_eq_zero, ← hr]
    ring
  replace hs : s^3 = (-1001 * s - 2008) / 8 := by
    cancel_denoms
    rw [← sub_eq_zero, ← hs]
    ring
  replace ht : t^3 = (-1001 * t - 2008) / 8 := by
    cancel_denoms
    rw [← sub_eq_zero, ← ht]
    ring
  rw [hr, hs, ht]
  -- Compute the sum
  rw [show -((-1001 * r - 2008) / 8 + (-1001 * s - 2008) / 8 + (-1001 * t - 2008) / 8) = (1001 * (r + s + t) + 6024) / 8 by ring, h1]
  norm_num
